// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! typed-wasm producer — **codegen v0**.
//!
//! This crate is the first in-tree `.twasm -> .wasm` producer. Before it,
//! the toolchain stopped at `source -> Lexer -> Parser -> Checker ->
//! diagnostics` and the only wasm-aware code was the *verifier*
//! (`typed-wasm-verify`). codegen v0 closes Phase 0's gate 2 (issue #48)
//! and seeds Phase 1 (issue #49) deliverable 1.
//!
//! ## What v0 does
//!
//! It lowers a typed region [`Module`] IR to:
//!   * a well-formed wasm module (memory + typed function bodies), and
//!   * the L2–L6 carrier sections `typedwasm.regions` (proposal 0001 /
//!     ADR-0002) and `typedwasm.access-sites` (proposal 0002 / ADR-0003),
//!
//! emitted via `typed-wasm-verify`'s *own* carrier encoders so the bytes
//! cannot drift from the decoder the verifier runs. The result round-trips
//! through [`typed_wasm_verify::verify_from_module`] and
//! `verify_access_sites_from_module` in-process (see `tests/roundtrip.rs`).
//!
//! ## What v0 does NOT do yet (deferred, see ADR-0004)
//!
//! * The front-end (AffineScript) → IR seam is unbuilt: v0 constructs the
//!   IR for [`example01`] directly rather than parsing `.twasm`. Wiring the
//!   checker's AST to this IR (a serialized JSON IR) is tracked by issue
//!   #127 (D1: all 10 levels × all 6 examples).
//! * L7/L10 ownership/linearity carriers (`typedwasm.ownership`) are
//!   emitted whenever the source declares discipline (`own` / `&mut` /
//!   `&` qualifiers) — the parser records them into [`Module::ownership`]
//!   and `emit` writes the carrier (exercised by `tests/example03.rs`).
//! * Function bodies lower for real where the statement lowerer covers
//!   them (`let`, assignment, `if`/`else`, `while`, indexed access,
//!   `cast<>`, `region.scan` closures with `where` predicates,
//!   `is_null` under the v0 null-is-zero convention — see `parser.rs`);
//!   handle-typed locals and embedded-region field paths still fall
//!   back to type-correct representative stubs.

use typed_wasm_verify::section::{
    build_access_sites_section_payload, AccessSiteEntry, ACCESS_SITE_UNPINNED, NO_TARGET_REGION,
};
use typed_wasm_verify::{
    build_ownership_section_payload, build_region_imports_section_payload,
    build_regions_section_payload, CrossError, FieldEntry, FieldKind,
    Nullability, OwnershipError, OwnershipEntry, OwnershipKind, RegionEntry,
    RegionImportEntry, VerifyError, WasmTy,
    verify_access_sites_from_module, verify_from_module,
    ACCESS_SITES_SECTION_NAME, OWNERSHIP_SECTION_NAME, REGIONS_SECTION_NAME,
    REGION_IMPORTS_SECTION_NAME,
};
use wasm_encoder::{
    BlockType, CodeSection, CustomSection, EntityType, ExportKind, ExportSection, Function, FunctionSection,
    ImportSection, Instruction, MemArg, MemorySection, MemoryType, Module as WasmModule,
    NameMap, NameSection, TypeSection, ValType,
};

pub mod parser;

// ----------------------------------------------------------------------
// Typed region IR
// ----------------------------------------------------------------------

/// A scalar field storage type. Maps 1:1 onto
/// [`typed_wasm_verify::WasmTy`] for the `typedwasm.regions` carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scalar {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
}

impl Scalar {
    fn to_wasm_ty(self) -> WasmTy {
        match self {
            Scalar::U8 => WasmTy::U8,
            Scalar::U16 => WasmTy::U16,
            Scalar::U32 => WasmTy::U32,
            Scalar::U64 => WasmTy::U64,
            Scalar::I8 => WasmTy::I8,
            Scalar::I16 => WasmTy::I16,
            Scalar::I32 => WasmTy::I32,
            Scalar::I64 => WasmTy::I64,
            Scalar::F32 => WasmTy::F32,
            Scalar::F64 => WasmTy::F64,
            Scalar::Bool => WasmTy::WBool,
        }
    }
}

/// Pointer/reference kind for a region-typed field (`@Region` / `opt<@Region>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtrKind {
    Owning,
    Borrow,
    Exclusive,
}

/// A field's type: either a scalar, or a reference to another region.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTy {
    Scalar(Scalar),
    /// Reference to region at `target` (index into [`Module::regions`]).
    Ptr {
        kind: PtrKind,
        target: usize,
        nullable: bool,
    },
}

/// One field of a region schema.
#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub ty: FieldTy,
    /// 1 = single value, n>1 = fixed array, 0 = unbounded/dynamic.
    pub cardinality: u32,
}

impl Field {
    pub fn scalar(name: &str, ty: Scalar) -> Self {
        Field {
            name: name.into(),
            ty: FieldTy::Scalar(ty),
            cardinality: 1,
        }
    }
    pub fn array(name: &str, ty: Scalar, len: u32) -> Self {
        Field {
            name: name.into(),
            ty: FieldTy::Scalar(ty),
            cardinality: len,
        }
    }
    pub fn ptr(name: &str, kind: PtrKind, target: usize, nullable: bool) -> Self {
        Field {
            name: name.into(),
            ty: FieldTy::Ptr {
                kind,
                target,
                nullable,
            },
            cardinality: 1,
        }
    }
}

/// A region schema (a "table" over linear memory).
#[derive(Debug, Clone)]
pub struct Region {
    pub name: String,
    pub fields: Vec<Field>,
    pub byte_size: u32,
}

/// A wasm value type usable as a function parameter/result in v0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Wty {
    I32,
    I64,
    F32,
    F64,
}

impl Wty {
    fn to_val_type(self) -> ValType {
        match self {
            Wty::I32 => ValType::I32,
            Wty::I64 => ValType::I64,
            Wty::F32 => ValType::F32,
            Wty::F64 => ValType::F64,
        }
    }
}

/// The minimal instruction set v0 lowers. Memory accesses carry only a
/// static offset (alignment is fixed to natural alignment); full address
/// arithmetic / indexing is deferred to #127.
#[derive(Debug, Clone, Copy)]
pub enum Op {
    LocalGet(u32),
    I32Const(i32),
    I64Const(i64),
    F32Const(f32),
    F64Const(f64),
    I32Load {
        offset: u64,
    },
    I32Store {
        offset: u64,
    },
    /// Sub-width integer accesses for 1- and 2-byte fields. The value on the
    /// wasm stack is i32; load8/load16 sign- (`S`) or zero- (`U`) extend, and
    /// store8/store16 write only the low byte(s) — so a narrow field touches
    /// exactly its own bytes, never the neighbour's.
    I32Load8U {
        offset: u64,
    },
    I32Load8S {
        offset: u64,
    },
    I32Load16U {
        offset: u64,
    },
    I32Load16S {
        offset: u64,
    },
    I32Store8 {
        offset: u64,
    },
    I32Store16 {
        offset: u64,
    },
    I64Load {
        offset: u64,
    },
    I64Store {
        offset: u64,
    },
    F32Load {
        offset: u64,
    },
    F32Store {
        offset: u64,
    },
    F64Load {
        offset: u64,
    },
    F64Store {
        offset: u64,
    },
    /// Call the function at the given global index (imports occupy the
    /// low indices). Used by the multi-module caller to invoke an import.
    Call(u32),
    /// Drop the top stack value — consumes a value exactly once.
    Drop,
    // --- Locals + control flow + arithmetic (front-end statement
    // lowering, ADR-0006: `let`, assignment, `if`/`else`, `while`) ---
    LocalSet(u32),
    LocalTee(u32),
    /// `block (empty)` — the `while` exit target.
    Block,
    /// `loop (empty)` — the `while` back-edge target.
    Loop,
    /// `if (empty)` — statement-position conditional (no result value).
    If,
    Else,
    End,
    Br(u32),
    BrIf(u32),
    Return,
    I32Eqz,
    I32And,
    I32Or,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LeS,
    I32GtS,
    I32GeS,
    I64Add,
    I64Sub,
    I64Mul,
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Eq,
    F32Ne,
    F32Lt,
    F32Le,
    F32Gt,
    F32Ge,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Eq,
    F64Ne,
    F64Lt,
    F64Le,
    F64Gt,
    F64Ge,
    /// `cast<i32>(f32/f64 expr)` — saturating-free truncation (traps on
    /// NaN/overflow, matching wasm core `i32.trunc_f*_s`).
    I32TruncF32S,
    I32TruncF64S,
    F32ConvertI32S,
    F64ConvertI32S,
}

/// Ownership discipline for a function parameter, emitted into the
/// `typedwasm.ownership` carrier (L7 aliasing / L10 linearity).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ownership {
    Unrestricted,
    Linear,
    SharedBorrow,
    ExclBorrow,
}

impl Ownership {
    fn to_kind(self) -> OwnershipKind {
        match self {
            Ownership::Unrestricted => OwnershipKind::Unrestricted,
            Ownership::Linear => OwnershipKind::Linear,
            Ownership::SharedBorrow => OwnershipKind::SharedBorrow,
            Ownership::ExclBorrow => OwnershipKind::ExclBorrow,
        }
    }
}

/// A function import (the cross-module boundary). Occupies a slot in the
/// module's function index space ahead of the local functions.
#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub field: String,
    pub params: Vec<Wty>,
    pub results: Vec<Wty>,
}

/// A typed access site: a load/store reaching `region`'s `field`,
/// recorded into `typedwasm.access-sites`.
#[derive(Debug, Clone, Copy)]
pub struct AccessSite {
    /// Index into [`Module::regions`].
    pub region: usize,
    /// Index into the target region's field list.
    pub field: usize,
    /// The 0-based instruction index (operator position) in the function
    /// body that this site pins — the load/store the verifier's L2
    /// access-typing pass checks against the field's type/width/offset.
    /// `None` = declared-only: the producer asserts the field is reached
    /// but does not pin a concrete instruction (representative /
    /// hand-written bodies). Emitted as [`ACCESS_SITE_UNPINNED`] on the
    /// wire. Closes proposal 0002's deferred `AccessSiteMisalignment`.
    pub instr_index: Option<usize>,
}

/// A function: a typed signature, a body, and the typed access sites its
/// body performs.
#[derive(Debug, Clone)]
pub struct Func {
    pub name: String,
    pub params: Vec<Wty>,
    pub results: Vec<Wty>,
    /// Extra (non-param) locals, indexed after the params. Statement
    /// lowering allocates these for `let` bindings, `region.get`
    /// destinations, and the per-handle base-pointer copies that keep
    /// L7/L10 param-use counts at exactly one.
    pub locals: Vec<Wty>,
    pub body: Vec<Op>,
    pub accesses: Vec<AccessSite>,
    pub export: bool,
}

/// A linear-memory declaration (wasm pages: 64 KiB each).
#[derive(Debug, Clone, Copy)]
pub struct Memory {
    pub min_pages: u64,
    pub max_pages: Option<u64>,
}

/// A complete typed-wasm module IR.
#[derive(Debug, Clone)]
pub struct Module {
    pub regions: Vec<Region>,
    /// Linear memory, if the module declares one. Region-bearing modules
    /// have memory; pure cross-module boundary modules need none.
    pub memory: Option<Memory>,
    /// Function imports (the cross-module boundary), ahead of `funcs` in
    /// the function index space.
    pub imports: Vec<Import>,
    pub funcs: Vec<Func>,
    /// Per-local-function ownership annotations: `(local_func_index,
    /// param_kinds, ret_kind)`. Emitted as the `typedwasm.ownership`
    /// carrier; empty = no L7/L10 carrier.
    pub ownership: Vec<(usize, Vec<Ownership>, Ownership)>,
    /// Cross-module region imports (`import region X from "module"`),
    /// each carrying the EXPECTED schema. Emitted as the
    /// `typedwasm.region-imports` carrier (proposal 0003 / ADR-0007,
    /// L13 positive form); empty = no carrier. Entries reuse the
    /// verifier's own type so bytes cannot drift from its decoder.
    pub region_imports: Vec<RegionImportEntry>,
}

// ----------------------------------------------------------------------
// Lowering: IR -> wasm bytes + carriers
// ----------------------------------------------------------------------

fn field_to_entry(f: &Field) -> FieldEntry {
    match f.ty {
        FieldTy::Scalar(s) => FieldEntry {
            name: f.name.clone(),
            kind: FieldKind::Scalar,
            wasm_ty: s.to_wasm_ty(),
            target_region: NO_TARGET_REGION,
            nullability: Nullability::NonNull,
            cardinality: f.cardinality,
        },
        FieldTy::Ptr {
            kind,
            target,
            nullable,
        } => FieldEntry {
            name: f.name.clone(),
            kind: match kind {
                PtrKind::Owning => FieldKind::PtrOwning,
                PtrKind::Borrow => FieldKind::PtrBorrow,
                PtrKind::Exclusive => FieldKind::PtrExclusive,
            },
            wasm_ty: WasmTy::NotApplicable,
            target_region: target as u32,
            nullability: if nullable {
                Nullability::Nullable
            } else {
                Nullability::NonNull
            },
            cardinality: f.cardinality,
        },
    }
}

fn op_to_instruction(op: Op) -> Instruction<'static> {
    // Natural alignment for the scalar widths v0 emits; align is the
    // log2 of the byte alignment.
    let memarg = |offset: u64, align: u32| MemArg {
        offset,
        align,
        memory_index: 0,
    };
    match op {
        Op::LocalGet(i) => Instruction::LocalGet(i),
        Op::I32Const(c) => Instruction::I32Const(c),
        Op::I64Const(c) => Instruction::I64Const(c),
        Op::F32Const(c) => Instruction::F32Const(c.into()),
        Op::F64Const(c) => Instruction::F64Const(c.into()),
        Op::I32Load { offset } => Instruction::I32Load(memarg(offset, 2)),
        Op::I32Store { offset } => Instruction::I32Store(memarg(offset, 2)),
        Op::I32Load8U { offset } => Instruction::I32Load8U(memarg(offset, 0)),
        Op::I32Load8S { offset } => Instruction::I32Load8S(memarg(offset, 0)),
        Op::I32Load16U { offset } => Instruction::I32Load16U(memarg(offset, 1)),
        Op::I32Load16S { offset } => Instruction::I32Load16S(memarg(offset, 1)),
        Op::I32Store8 { offset } => Instruction::I32Store8(memarg(offset, 0)),
        Op::I32Store16 { offset } => Instruction::I32Store16(memarg(offset, 1)),
        Op::I64Load { offset } => Instruction::I64Load(memarg(offset, 3)),
        Op::I64Store { offset } => Instruction::I64Store(memarg(offset, 3)),
        Op::F32Load { offset } => Instruction::F32Load(memarg(offset, 2)),
        Op::F32Store { offset } => Instruction::F32Store(memarg(offset, 2)),
        Op::F64Load { offset } => Instruction::F64Load(memarg(offset, 3)),
        Op::F64Store { offset } => Instruction::F64Store(memarg(offset, 3)),
        Op::Call(i) => Instruction::Call(i),
        Op::Drop => Instruction::Drop,
        Op::LocalSet(i) => Instruction::LocalSet(i),
        Op::LocalTee(i) => Instruction::LocalTee(i),
        Op::Block => Instruction::Block(BlockType::Empty),
        Op::Loop => Instruction::Loop(BlockType::Empty),
        Op::If => Instruction::If(BlockType::Empty),
        Op::Else => Instruction::Else,
        Op::End => Instruction::End,
        Op::Br(d) => Instruction::Br(d),
        Op::BrIf(d) => Instruction::BrIf(d),
        Op::Return => Instruction::Return,
        Op::I32Eqz => Instruction::I32Eqz,
        Op::I32And => Instruction::I32And,
        Op::I32Or => Instruction::I32Or,
        Op::I32Add => Instruction::I32Add,
        Op::I32Sub => Instruction::I32Sub,
        Op::I32Mul => Instruction::I32Mul,
        Op::I32DivS => Instruction::I32DivS,
        Op::I32Eq => Instruction::I32Eq,
        Op::I32Ne => Instruction::I32Ne,
        Op::I32LtS => Instruction::I32LtS,
        Op::I32LeS => Instruction::I32LeS,
        Op::I32GtS => Instruction::I32GtS,
        Op::I32GeS => Instruction::I32GeS,
        Op::I64Add => Instruction::I64Add,
        Op::I64Sub => Instruction::I64Sub,
        Op::I64Mul => Instruction::I64Mul,
        Op::F32Add => Instruction::F32Add,
        Op::F32Sub => Instruction::F32Sub,
        Op::F32Mul => Instruction::F32Mul,
        Op::F32Div => Instruction::F32Div,
        Op::F32Eq => Instruction::F32Eq,
        Op::F32Ne => Instruction::F32Ne,
        Op::F32Lt => Instruction::F32Lt,
        Op::F32Le => Instruction::F32Le,
        Op::F32Gt => Instruction::F32Gt,
        Op::F32Ge => Instruction::F32Ge,
        Op::F64Add => Instruction::F64Add,
        Op::F64Sub => Instruction::F64Sub,
        Op::F64Mul => Instruction::F64Mul,
        Op::F64Div => Instruction::F64Div,
        Op::F64Eq => Instruction::F64Eq,
        Op::F64Ne => Instruction::F64Ne,
        Op::F64Lt => Instruction::F64Lt,
        Op::F64Le => Instruction::F64Le,
        Op::F64Gt => Instruction::F64Gt,
        Op::F64Ge => Instruction::F64Ge,
        Op::I32TruncF32S => Instruction::I32TruncF32S,
        Op::I32TruncF64S => Instruction::I32TruncF64S,
        Op::F32ConvertI32S => Instruction::F32ConvertI32S,
        Op::F64ConvertI32S => Instruction::F64ConvertI32S,
    }
}

/// Lower a typed-wasm [`Module`] IR to a wasm binary with embedded
/// `typedwasm.*` carrier sections (`ownership`, `regions`,
/// `access-sites`), each emitted only when it has content.
///
/// Section order is the canonical wasm ordering (Type, Import, Function,
/// Memory, Export, Code, then custom sections) so the output passes a full
/// wasm validator, not just a lenient parser. Imports occupy the low
/// function indices, so a local function's global index is
/// `imports.len() + local_index`.
pub fn emit(module: &Module) -> Vec<u8> {
    let import_count = module.imports.len() as u32;

    // Types: one per import (low type indices), then one per local function.
    let mut types = TypeSection::new();
    for im in &module.imports {
        let params: Vec<ValType> = im.params.iter().map(|w| w.to_val_type()).collect();
        let results: Vec<ValType> = im.results.iter().map(|w| w.to_val_type()).collect();
        types.ty().function(params, results);
    }
    for func in &module.funcs {
        let params: Vec<ValType> = func.params.iter().map(|w| w.to_val_type()).collect();
        let results: Vec<ValType> = func.results.iter().map(|w| w.to_val_type()).collect();
        types.ty().function(params, results);
    }

    let mut imports = ImportSection::new();
    for (i, im) in module.imports.iter().enumerate() {
        imports.import(&im.module, &im.field, EntityType::Function(i as u32));
    }

    let mut funcs = FunctionSection::new();
    let mut code = CodeSection::new();
    let mut exports = ExportSection::new();
    let mut access_entries: Vec<AccessSiteEntry> = Vec::new();

    for (local_i, func) in module.funcs.iter().enumerate() {
        // Type index and global function index both account for the
        // imports that precede the local functions.
        let global_idx = import_count + local_i as u32;
        funcs.function(global_idx);

        let mut f =
            Function::new_with_locals_types(func.locals.iter().map(|l| l.to_val_type()));
        for op in &func.body {
            f.instruction(&op_to_instruction(*op));
        }
        f.instruction(&Instruction::End);
        code.function(&f);

        if func.export {
            exports.export(&func.name, ExportKind::Func, global_idx);
        }

        for site in &func.accesses {
            access_entries.push(AccessSiteEntry {
                func_idx: global_idx,
                // The wire slot carries the pinned instruction index, or
                // the unpinned sentinel for declared-only sites.
                instruction_byte_offset: site
                    .instr_index
                    .map(|k| k as u32)
                    .unwrap_or(ACCESS_SITE_UNPINNED),
                region_id: site.region as u32,
                field_id: site.field as u32,
            });
        }
    }

    // typedwasm.ownership carrier (L7/L10), keyed by GLOBAL function index.
    let ownership_entries: Vec<OwnershipEntry> = module
        .ownership
        .iter()
        .map(|(local_i, kinds, ret)| OwnershipEntry {
            func_idx: import_count + *local_i as u32,
            param_kinds: kinds.iter().map(|o| o.to_kind()).collect(),
            ret_kind: ret.to_kind(),
        })
        .collect();

    // L2–L6 region schema carrier.
    let region_entries: Vec<RegionEntry> = module
        .regions
        .iter()
        .map(|r| RegionEntry {
            name: r.name.clone(),
            fields: r.fields.iter().map(field_to_entry).collect(),
            region_byte_size: r.byte_size,
        })
        .collect();

    let mut wasm = WasmModule::new();
    wasm.section(&types);
    if import_count > 0 {
        wasm.section(&imports);
    }
    wasm.section(&funcs);
    if let Some(mem) = &module.memory {
        let mut mems = MemorySection::new();
        mems.memory(MemoryType {
            minimum: mem.min_pages,
            maximum: mem.max_pages,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        wasm.section(&mems);
    }
    wasm.section(&exports);
    wasm.section(&code);

    // Name section: function names for debugging (wasm name custom section)
    if !module.funcs.is_empty() {
        let mut names = NameSection::new();
        let mut function_names = NameMap::new();
        for (i, func) in module.funcs.iter().enumerate() {
            function_names.append(import_count + i as u32, &func.name);
        }
        names.functions(&function_names);
        wasm.section(&names);
    }

    // Carriers — each only when non-empty (an access-sites section without
    // a companion regions section is a verifier hard error).
    if !ownership_entries.is_empty() {
        let payload = build_ownership_section_payload(&ownership_entries);
        wasm.section(&CustomSection {
            name: OWNERSHIP_SECTION_NAME.into(),
            data: payload.as_slice().into(),
        });
    }
    // Region imports require their dependent regions carrier (proposal
    // 0003 §Producer obligations #1) — emit regions (even if empty)
    // whenever an import table is present.
    if !region_entries.is_empty() || !module.region_imports.is_empty() {
        let payload = build_regions_section_payload(&region_entries);
        wasm.section(&CustomSection {
            name: REGIONS_SECTION_NAME.into(),
            data: payload.as_slice().into(),
        });
    }
    if !module.region_imports.is_empty() {
        let payload = build_region_imports_section_payload(&module.region_imports);
        wasm.section(&CustomSection {
            name: REGION_IMPORTS_SECTION_NAME.into(),
            data: payload.as_slice().into(),
        });
    }
    if !access_entries.is_empty() {
        let payload = build_access_sites_section_payload(&access_entries);
        wasm.section(&CustomSection {
            name: ACCESS_SITES_SECTION_NAME.into(),
            data: payload.as_slice().into(),
        });
    }
    wasm.finish()
}

// ----------------------------------------------------------------------
// example01: the IR for examples/01-single-module.twasm
// ----------------------------------------------------------------------

/// Build the typed region IR corresponding to
/// `examples/01-single-module.twasm` (regions `Vec2`, `Players[100]`,
/// `Enemies[256]`; `memory game_memory`; five typed-access functions).
///
/// This is the v0 stand-in for `parse(examples/01...)`. The front-end →
/// IR bridge is deferred per ADR-0004 (tracked by #127).
pub fn example01() -> Module {
    // Region indices: Vec2 = 0, Players = 1, Enemies = 2.
    let vec2 = Region {
        name: "Vec2".into(),
        fields: vec![
            Field::scalar("x", Scalar::F32),
            Field::scalar("y", Scalar::F32),
        ],
        byte_size: 8,
    };
    let players = Region {
        name: "Players".into(),
        fields: vec![
            Field::scalar("hp", Scalar::I32),             // field 0
            Field::scalar("speed", Scalar::F64),          // field 1
            Field::ptr("pos", PtrKind::Owning, 0, false), // field 2 -> Vec2
            Field::array("name", Scalar::U8, 24),         // field 3
        ],
        byte_size: 48,
    };
    let enemies = Region {
        name: "Enemies".into(),
        fields: vec![
            Field::scalar("hp", Scalar::I32),               // field 0
            Field::scalar("damage", Scalar::I32),           // field 1
            Field::ptr("target", PtrKind::Borrow, 1, true), // field 2 -> opt<@Players>
            Field::ptr("pos", PtrKind::Owning, 0, false),   // field 3 -> Vec2
            Field::scalar("is_active", Scalar::Bool),       // field 4
        ],
        byte_size: 24,
    };

    let funcs = vec![
        // 0: get_player_hp(players, idx) -> i32   (L2/L3/L6: Players.hp)
        Func {
            name: "get_player_hp".into(),
            params: vec![Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
            accesses: vec![AccessSite {
                region: 1,
                field: 0,
                instr_index: None,
            }],
            export: true,
        },
        // 1: damage_player(players, idx, amount)  (L3/L8: write Players.hp)
        Func {
            name: "damage_player".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::LocalGet(2), Op::I32Store { offset: 0 }],
            accesses: vec![AccessSite {
                region: 1,
                field: 0,
                instr_index: None,
            }],
            export: true,
        },
        // 2: get_enemy_target_hp(enemies, players, enemy_idx) -> i32
        //    (L4 null safety: Enemies.target; then Players.hp)
        Func {
            name: "get_enemy_target_hp".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
            accesses: vec![
                AccessSite {
                    region: 2,
                    field: 2,
                    instr_index: None,
                }, // Enemies.target
                AccessSite {
                    region: 1,
                    field: 0,
                    instr_index: None,
                }, // Players.hp
            ],
            export: true,
        },
        // 3: count_active_enemies(enemies) -> i32  (L2/L6: Enemies.is_active)
        Func {
            name: "count_active_enemies".into(),
            params: vec![Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![Op::I32Const(0)],
            accesses: vec![AccessSite {
                region: 2,
                field: 4,
                instr_index: None,
            }],
            export: true,
        },
        // 4: move_player(players, idx, dx, dy)     (nested: Players.pos)
        Func {
            name: "move_player".into(),
            params: vec![Wty::I32, Wty::I32, Wty::F32, Wty::F32],
            results: vec![],
            locals: vec![],
            body: vec![
                Op::LocalGet(0),
                Op::LocalGet(2),
                Op::F32Store { offset: 16 },
            ],
            accesses: vec![AccessSite {
                region: 1,
                field: 2,
                instr_index: None,
            }],
            export: true,
        },
    ];

    Module {
        regions: vec![vec2, players, enemies],
        memory: Some(Memory {
            min_pages: 64,
            max_pages: Some(256),
        }),
        imports: vec![],
        funcs,
        ownership: vec![],
        region_imports: vec![],
    }
}

/// Convenience: lower [`example01`] to wasm bytes.
pub fn emit_example01() -> Vec<u8> {
    emit(&example01())
}

// ----------------------------------------------------------------------
// Paint-type bridge schemas (paint-type#39)
// ----------------------------------------------------------------------

/// Paint-type tile schema IR (paint-type-tile.twasm).
/// Region indices: RGBA16F = 0, TileHeader = 1, Tile = 2.
pub fn paint_type_tile() -> Module {
    // RGBA16F: r:u16, g:u16, b:u16, a:u16 (8 bytes, align 2)
    let rgba16f = Region {
        name: "RGBA16F".into(),
        fields: vec![
            Field::scalar("r", Scalar::U16),
            Field::scalar("g", Scalar::U16),
            Field::scalar("b", Scalar::U16),
            Field::scalar("a", Scalar::U16),
        ],
        byte_size: 8,
    };
    
    // TileHeader: magic:u32, version:u32, grid_x:u32, grid_y:u32 (16 bytes, align 4)
    let tile_header = Region {
        name: "TileHeader".into(),
        fields: vec![
            Field::scalar("magic", Scalar::U32),
            Field::scalar("version", Scalar::U32),
            Field::scalar("grid_x", Scalar::U32),
            Field::scalar("grid_y", Scalar::U32),
        ],
        byte_size: 16,
    };
    
    // Tile: header:@TileHeader, pixels:@RGBA16F[4096] (32784 bytes)
    let tile = Region {
        name: "Tile".into(),
        fields: vec![
            Field::ptr("header", PtrKind::Owning, 1, false), // -> TileHeader
            Field::array("pixels", Scalar::U16, 4096 * 4), // 4096 pixels * 4 channels = 16384 u16 elements
        ],
        byte_size: 32784,
    };

    let funcs = vec![
        // alloc_tile(grid_x: u32, grid_y: u32) -> own region<Tile>
        // Body: local.get 0, drop, i32.const 0 (consume params, return 0)
        Func {
            name: "alloc_tile".into(),
            params: vec![Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::Drop, Op::I32Const(0)],
            accesses: vec![],
            export: true,
        },
        // free_tile(tile: own region<Tile>)
        // Body: local.get 0, drop
        Func {
            name: "free_tile".into(),
            params: vec![Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::Drop],
            accesses: vec![],
            export: true,
        },
        // fill_tile(tile: &mut region<Tile>, r: u16, g: u16, b: u16, a: u16)
        // Body: local.get 0..4, drop all
        Func {
            name: "fill_tile".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32, Wty::I32, Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
                Op::LocalGet(2), Op::Drop,
                Op::LocalGet(3), Op::Drop,
                Op::LocalGet(4), Op::Drop,
            ],
            accesses: vec![
                AccessSite { region: 2, field: 1, instr_index: None },
            ],
            export: true,
        },
        // read_pixel(tile: &region<Tile>, idx_x: i32, idx_y: i32) -> @RGBA16F
        // Body: local.get 0, drop, i32.const 0
        Func {
            name: "read_pixel".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
                Op::I32Const(0),
            ],
            accesses: vec![
                AccessSite { region: 2, field: 1, instr_index: None },
            ],
            export: true,
        },
        // write_pixel(tile: &mut region<Tile>, idx_x: i32, idx_y: i32, r: u16, g: u16, b: u16, a: u16)
        // Body: drop all params
        Func {
            name: "write_pixel".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32, Wty::I32, Wty::I32, Wty::I32, Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
                Op::LocalGet(2), Op::Drop,
                Op::LocalGet(3), Op::Drop,
                Op::LocalGet(4), Op::Drop,
                Op::LocalGet(5), Op::Drop,
                Op::LocalGet(6), Op::Drop,
            ],
            accesses: vec![
                AccessSite { region: 2, field: 1, instr_index: None },
            ],
            export: true,
        },
        // blit_tile(dst: &mut region<Tile>, src: &region<Tile>)
        // Body: drop both params
        Func {
            name: "blit_tile".into(),
            params: vec![Wty::I32, Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
            ],
            accesses: vec![
                AccessSite { region: 2, field: 1, instr_index: None },
            ],
            export: true,
        },
    ];

    Module {
        regions: vec![rgba16f, tile_header, tile],
        memory: Some(Memory {
            min_pages: 1,
            max_pages: Some(1024),
        }),
        imports: vec![],
        funcs,
        ownership: vec![],
        region_imports: vec![],
    }
}

/// Convenience: lower [`paint_type_tile`] to wasm bytes.
pub fn emit_paint_type_tile() -> Vec<u8> {
    emit(&paint_type_tile())
}

/// Paint-type layer schema IR (paint-type-layer.twasm).
/// Region indices: LayerName = 0, Layer = 1, LayerStack = 2.
pub fn paint_type_layer() -> Module {
    // LayerName: bytes:u8[256] (256 bytes, align 1)
    let layer_name = Region {
        name: "LayerName".into(),
        fields: vec![
            Field::array("bytes", Scalar::U8, 256),
        ],
        byte_size: 256,
    };
    
    // Layer: id:u32, name_len:u32, opacity_bits:u32, visible:u32, name:@LayerName (272 bytes)
    let layer = Region {
        name: "Layer".into(),
        fields: vec![
            Field::scalar("id", Scalar::U32),
            Field::scalar("name_len", Scalar::U32),
            Field::scalar("opacity_bits", Scalar::U32),
            Field::scalar("visible", Scalar::U32),
            Field::ptr("name", PtrKind::Owning, 0, false), // -> LayerName
        ],
        byte_size: 272,
    };
    
    // LayerStack: magic:u32, layer_count:u32, next_id:u32, _pad:u32, layers:@Layer[256] (16 + 256*272 = 70128 bytes)
    let layer_stack = Region {
        name: "LayerStack".into(),
        fields: vec![
            Field::scalar("magic", Scalar::U32),
            Field::scalar("layer_count", Scalar::U32),
            Field::scalar("next_id", Scalar::U32),
            Field::scalar("_pad", Scalar::U32),
            Field::array("layers", Scalar::U8, 256 * 272), // placeholder as bytes for v0
        ],
        byte_size: 70128,
    };

    let funcs = vec![
        // stack_new() -> own region<LayerStack>
        Func {
            name: "stack_new".into(),
            params: vec![],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![Op::I32Const(0)],
            accesses: vec![],
            export: true,
        },
        // stack_free(stack: own region<LayerStack>)
        Func {
            name: "stack_free".into(),
            params: vec![Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::Drop],
            accesses: vec![],
            export: true,
        },
        // push_layer(stack: &mut region<LayerStack>, name_buf: &region<LayerName>, name_len: u32) -> u32
        Func {
            name: "push_layer".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
                Op::LocalGet(2), Op::Drop,
                Op::I32Const(0),
            ],
            accesses: vec![
                AccessSite { region: 2, field: 0, instr_index: None },
                AccessSite { region: 2, field: 1, instr_index: None },
                AccessSite { region: 2, field: 2, instr_index: None },
            ],
            export: true,
        },
        // get_id_at(stack: &region<LayerStack>, position: u32) -> u32
        Func {
            name: "get_id_at".into(),
            params: vec![Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
                Op::I32Const(0),
            ],
            accesses: vec![
                AccessSite { region: 2, field: 1, instr_index: None },
            ],
            export: true,
        },
        // set_opacity(stack: &mut region<LayerStack>, id: u32, bits: u32) -> u32
        Func {
            name: "set_opacity".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            locals: vec![],
            body: vec![
                Op::LocalGet(0), Op::Drop,
                Op::LocalGet(1), Op::Drop,
                Op::LocalGet(2), Op::Drop,
                Op::I32Const(0),
            ],
            accesses: vec![
                AccessSite { region: 2, field: 1, instr_index: None },
            ],
            export: true,
        },
    ];

    Module {
        regions: vec![layer_name, layer, layer_stack],
        memory: Some(Memory {
            min_pages: 2,
            max_pages: Some(2),
        }),
        imports: vec![],
        funcs,
        ownership: vec![],
        region_imports: vec![],
    }
}

/// Convenience: lower [`paint_type_layer`] to wasm bytes.
pub fn emit_paint_type_layer() -> Vec<u8> {
    emit(&paint_type_layer())
}

// ----------------------------------------------------------------------
// Multi-module codegen — Phase 1 deliverable 7 (#128)
//
// Producer-side emission at parity with the verifier's *existing*
// cross-module coverage: the L10 linear-ownership import boundary
// (`typed_wasm_verify::verify_cross_module`). A callee module exports a
// Linear-consuming function (recorded in `typedwasm.ownership`); a caller
// module imports it and must call it exactly once per path.
//
// The L13 *positive-form* shared-region schema agreement that
// `examples/02-multi-module.twasm` illustrates (`export region` /
// `import region ... from`) rides the `typedwasm.region-imports` carrier —
// proposal 0003 `[draft]`, with no verifier pass yet — so it is out of
// scope here and tracked separately.
// ----------------------------------------------------------------------

/// The callee module: exports `consume` — one Linear param, consumed
/// exactly once — with a `typedwasm.ownership` carrier so a consumer's
/// verifier can read the boundary contract via `extract_exports`.
pub fn multimodule_callee() -> Module {
    Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "consume".into(),
            params: vec![Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::Drop], // uses the Linear param once
            accesses: vec![],
            export: true,
        }],
        ownership: vec![(0, vec![Ownership::Linear], Ownership::Unrestricted)],
        region_imports: vec![],
    }
}

/// A caller module importing the callee's `consume` and calling it
/// `call_count` times in its single function. `call_count == 1` is the
/// clean linear transfer; `>= 2` duplicates the resource and must be
/// rejected by `verify_cross_module`.
pub fn multimodule_caller(call_count: u32) -> Module {
    let mut body = Vec::new();
    for _ in 0..call_count {
        body.push(Op::LocalGet(0));
        body.push(Op::Call(0)); // the import occupies global function index 0
    }
    Module {
        regions: vec![],
        memory: None,
        imports: vec![Import {
            module: "callee".into(),
            field: "consume".into(), // must match the callee's export name
            params: vec![Wty::I32],
            results: vec![],
        }],
        funcs: vec![Func {
            name: "use_resource".into(),
            params: vec![Wty::I32],
            results: vec![],
            locals: vec![],
            body,
            accesses: vec![],
            export: false,
        }],
        ownership: vec![],
        region_imports: vec![],
    }
}

/// Convenience: emit the `(callee, caller)` pair for the clean
/// single-call linear transfer.
pub fn emit_multimodule() -> (Vec<u8>, Vec<u8>) {
    (emit(&multimodule_callee()), emit(&multimodule_caller(1)))
}

// ----------------------------------------------------------------------
// WAT (text wasm) emission — Phase 1 deliverable 4 (#125)
// ----------------------------------------------------------------------

/// Render a wasm binary to its WAT (text) form for debugging.
///
/// `wasmprinter` faithfully renders the module the emitter produced,
/// including the `typedwasm.*` custom sections, so the text view shows
/// the carriers alongside the code.
///
/// # Panics
///
/// Panics only if `wasm_bytes` is not well-formed wasm. [`emit`] always
/// produces well-formed wasm (see `tests/roundtrip.rs`), so this never
/// panics on emitter output; pass emitter output, not arbitrary bytes.
pub fn wat(wasm_bytes: &[u8]) -> String {
    wasmprinter::print_bytes(wasm_bytes).expect("emitted wasm is well-formed and prints to WAT")
}

/// Lower a [`Module`] to WAT (text wasm) — the textual companion of [`emit`].
pub fn emit_wat(module: &Module) -> String {
    wat(&emit(module))
}

/// Convenience: WAT for [`example01`].
pub fn emit_example01_wat() -> String {
    emit_wat(&example01())
}

// ----------------------------------------------------------------------
// Human-readable error helpers — Phase 1 deliverable 6 (#126).
// ----------------------------------------------------------------------

/// Self-verify a module: emit it to wasm bytes and run the verifier.
/// Returns `Ok(())` if verification passes, or `Err` with a list of
/// human-readable diagnostic strings if it fails.
pub fn self_verify(module: &Module) -> Result<(), Vec<String>> {
    let bytes = emit(module);
    match verify_from_module(&bytes) {
        Ok(()) => {
            // Also verify access sites
            let violations = verify_access_sites_from_module(&bytes)
                .map_err(|e| vec![format!("access-sites parse error: {e}")])?;
            if violations.is_empty() {
                Ok(())
            } else {
                Err(violations.into_iter().map(|v| format!("{v:?}")).collect())
            }
        }
        Err(e) => Err(humanize(module, &e)),
    }
}

/// Humanize a verification error by resolving function indices to names.
/// Takes the module IR (for name resolution) and the verifier error, and
/// returns a list of human-readable diagnostic strings.
pub fn humanize(module: &Module, err: &VerifyError) -> Vec<String> {
    match err {
        VerifyError::Parse(e) => vec![format!("wasm parse error: {e}")],
        VerifyError::Ownership(errs) => {
            errs.iter()
                .map(|e| humanize_ownership_error(module, e))
                .collect()
        }
        VerifyError::Cross(errs) => {
            errs.iter()
                .map(|e| humanize_cross_error(module, e))
                .collect()
        }
    }
}

/// Extract the function index from an OwnershipError.
fn func_idx(err: &OwnershipError) -> u32 {
    match err {
        OwnershipError::LinearNotUsed { func_idx, .. } => *func_idx,
        OwnershipError::LinearDroppedOnSomePath { func_idx, .. } => *func_idx,
        OwnershipError::LinearUsedMultiple { func_idx, .. } => *func_idx,
        OwnershipError::ExclBorrowAliased { func_idx, .. } => *func_idx,
        OwnershipError::ModuleNotIsolated { .. } => 0, // No function index for module-level errors
    }
}

fn humanize_ownership_error(module: &Module, err: &OwnershipError) -> String {
    // Map the func_idx to the actual function name
    let idx = func_idx(err);
    let func_name = module.funcs.get(idx as usize)
        .map(|f| f.name.clone())
        .unwrap_or_else(|| format!("function#{}", idx));
    
    match err {
        OwnershipError::LinearNotUsed { param_idx, .. } => {
            format!(
                "L10 (linearity): {} parameter #{} is a Linear (own) resource but is not used on any path; Linear resources must be consumed exactly once",
                func_name, param_idx
            )
        }
        OwnershipError::LinearDroppedOnSomePath { param_idx, .. } => {
            format!(
                "L10 (linearity): {} parameter #{} is a Linear (own) resource but is dropped on some paths (must be consumed on every path)",
                func_name, param_idx
            )
        }
        OwnershipError::LinearUsedMultiple { param_idx, count, .. } => {
            format!(
                "L10 (linearity): {} parameter #{} is a Linear (own) resource but is used {} times on some control-flow path; Linear resources must be consumed exactly once (possible duplication)",
                func_name, param_idx, count
            )
        }
        OwnershipError::ExclBorrowAliased { param_idx, count, .. } => {
            format!(
                "L7 (aliasing): {} parameter #{} is an ExclBorrow (&mut) reference but {} simultaneous borrows occur on some control-flow path; at most one is permitted",
                func_name, param_idx, count
            )
        }
        OwnershipError::ModuleNotIsolated { reason } => {
            format!("L13 (isolation): {}", reason)
        }
    }
}

/// Extract the caller function index from a CrossError.
fn caller_func_idx(err: &CrossError) -> u32 {
    match err {
        CrossError::LinearImportCalledMultiple { caller_func_idx, .. } => *caller_func_idx,
        CrossError::LinearImportDroppedOnSomePath { caller_func_idx, .. } => *caller_func_idx,
    }
}

fn humanize_cross_error(module: &Module, err: &CrossError) -> String {
    let idx = caller_func_idx(err);
    let func_name = module.funcs.get(idx as usize)
        .map(|f| f.name.clone())
        .unwrap_or_else(|| format!("function#{}", idx));
    
    match err {
        CrossError::LinearImportCalledMultiple { import_name, count, .. } => {
            format!(
                "L10 (boundary): {} calls import '{}' {} times on some path (Linear param; must be called at most once)",
                func_name, import_name, count
            )
        }
        CrossError::LinearImportDroppedOnSomePath { import_name, .. } => {
            format!(
                "L10 (boundary): {} calls import '{}' on some paths but not others (Linear param dropped on zero-call path)",
                func_name, import_name
            )
        }
    }
}
