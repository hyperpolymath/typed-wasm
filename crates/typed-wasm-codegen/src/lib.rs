// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
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
//! * L7/L10 ownership/linearity carriers (`typedwasm.ownership`) are not
//!   emitted for the read/write example 01 (its region borrows are not
//!   linear resources); they land with `examples/03-ownership-linearity`
//!   under #127.
//! * Full function-body semantics (indexing, `region.scan`, null checks):
//!   v0 emits type-correct representative bodies, not the full lowering.

use typed_wasm_verify::section::{
    build_access_sites_section_payload, AccessSiteEntry, NO_TARGET_REGION,
};
use typed_wasm_verify::{
    build_regions_section_payload, FieldEntry, FieldKind, Nullability, RegionEntry, WasmTy,
    ACCESS_SITES_SECTION_NAME, REGIONS_SECTION_NAME,
};
use wasm_encoder::{
    CodeSection, CustomSection, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    MemArg, MemorySection, MemoryType, Module as WasmModule, TypeSection, ValType,
};

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
    I32Load { offset: u64 },
    I32Store { offset: u64 },
    F32Load { offset: u64 },
    F32Store { offset: u64 },
}

/// A typed access site: the load/store at `offset` (bytes into the function
/// body) reaches `region`'s `field`. Recorded into `typedwasm.access-sites`.
#[derive(Debug, Clone, Copy)]
pub struct AccessSite {
    /// Index into [`Module::regions`].
    pub region: usize,
    /// Index into the target region's field list.
    pub field: usize,
    /// Instruction byte offset within the function body. v0 uses
    /// representative offsets; the verifier does not check offset
    /// alignment (proposal 0002 defers `AccessSiteMisalignment`).
    pub offset: u32,
}

/// A function: a typed signature, a body, and the typed access sites its
/// body performs.
#[derive(Debug, Clone)]
pub struct Func {
    pub name: String,
    pub params: Vec<Wty>,
    pub results: Vec<Wty>,
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
    pub memory: Memory,
    pub funcs: Vec<Func>,
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
        Op::I32Load { offset } => Instruction::I32Load(memarg(offset, 2)),
        Op::I32Store { offset } => Instruction::I32Store(memarg(offset, 2)),
        Op::F32Load { offset } => Instruction::F32Load(memarg(offset, 2)),
        Op::F32Store { offset } => Instruction::F32Store(memarg(offset, 2)),
    }
}

/// Lower a typed-wasm [`Module`] IR to a wasm binary with embedded
/// `typedwasm.regions` and `typedwasm.access-sites` carrier sections.
///
/// Section order is the canonical wasm ordering
/// (Type, Function, Memory, Export, Code, then custom sections) so the
/// output passes a full wasm validator, not just a lenient parser.
pub fn emit(module: &Module) -> Vec<u8> {
    let mut types = TypeSection::new();
    let mut funcs = FunctionSection::new();
    let mut code = CodeSection::new();
    let mut exports = ExportSection::new();
    let mut mems = MemorySection::new();

    mems.memory(MemoryType {
        minimum: module.memory.min_pages,
        maximum: module.memory.max_pages,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut access_entries: Vec<AccessSiteEntry> = Vec::new();

    for (func_idx, func) in module.funcs.iter().enumerate() {
        // One type per function (duplicate types are legal wasm); type
        // index lines up with function index since there are no imports.
        let params: Vec<ValType> = func.params.iter().map(|w| w.to_val_type()).collect();
        let results: Vec<ValType> = func.results.iter().map(|w| w.to_val_type()).collect();
        types.ty().function(params, results);
        funcs.function(func_idx as u32);

        let mut f = Function::new([]);
        for op in &func.body {
            f.instruction(&op_to_instruction(*op));
        }
        f.instruction(&Instruction::End);
        code.function(&f);

        if func.export {
            exports.export(&func.name, ExportKind::Func, func_idx as u32);
        }

        for site in &func.accesses {
            access_entries.push(AccessSiteEntry {
                func_idx: func_idx as u32,
                instruction_byte_offset: site.offset,
                region_id: site.region as u32,
                field_id: site.field as u32,
            });
        }
    }

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
    let regions_payload = build_regions_section_payload(&region_entries);
    let access_payload = build_access_sites_section_payload(&access_entries);

    let mut wasm = WasmModule::new();
    wasm.section(&types);
    wasm.section(&funcs);
    wasm.section(&mems);
    wasm.section(&exports);
    wasm.section(&code);
    wasm.section(&CustomSection {
        name: REGIONS_SECTION_NAME.into(),
        data: regions_payload.as_slice().into(),
    });
    wasm.section(&CustomSection {
        name: ACCESS_SITES_SECTION_NAME.into(),
        data: access_payload.as_slice().into(),
    });
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
            body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
            accesses: vec![AccessSite {
                region: 1,
                field: 0,
                offset: 6,
            }],
            export: true,
        },
        // 1: damage_player(players, idx, amount)  (L3/L8: write Players.hp)
        Func {
            name: "damage_player".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![],
            body: vec![Op::LocalGet(0), Op::LocalGet(2), Op::I32Store { offset: 0 }],
            accesses: vec![AccessSite {
                region: 1,
                field: 0,
                offset: 6,
            }],
            export: true,
        },
        // 2: get_enemy_target_hp(enemies, players, enemy_idx) -> i32
        //    (L4 null safety: Enemies.target; then Players.hp)
        Func {
            name: "get_enemy_target_hp".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
            accesses: vec![
                AccessSite {
                    region: 2,
                    field: 2,
                    offset: 6,
                }, // Enemies.target
                AccessSite {
                    region: 1,
                    field: 0,
                    offset: 9,
                }, // Players.hp
            ],
            export: true,
        },
        // 3: count_active_enemies(enemies) -> i32  (L2/L6: Enemies.is_active)
        Func {
            name: "count_active_enemies".into(),
            params: vec![Wty::I32],
            results: vec![Wty::I32],
            body: vec![Op::I32Const(0)],
            accesses: vec![AccessSite {
                region: 2,
                field: 4,
                offset: 2,
            }],
            export: true,
        },
        // 4: move_player(players, idx, dx, dy)     (nested: Players.pos)
        Func {
            name: "move_player".into(),
            params: vec![Wty::I32, Wty::I32, Wty::F32, Wty::F32],
            results: vec![],
            body: vec![
                Op::LocalGet(0),
                Op::LocalGet(2),
                Op::F32Store { offset: 16 },
            ],
            accesses: vec![AccessSite {
                region: 1,
                field: 2,
                offset: 6,
            }],
            export: true,
        },
    ];

    Module {
        regions: vec![vec2, players, enemies],
        memory: Memory {
            min_pages: 64,
            max_pages: Some(256),
        },
        funcs,
    }
}

/// Convenience: lower [`example01`] to wasm bytes.
pub fn emit_example01() -> Vec<u8> {
    emit(&example01())
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
