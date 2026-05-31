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
    build_ownership_section_payload, build_regions_section_payload, FieldEntry, FieldKind,
    Nullability, OwnershipEntry, OwnershipKind, RegionEntry, WasmTy, ACCESS_SITES_SECTION_NAME,
    OWNERSHIP_SECTION_NAME, REGIONS_SECTION_NAME,
};
use wasm_encoder::{
    CodeSection, CustomSection, EntityType, ExportKind, ExportSection, Function, FunctionSection,
    ImportSection, Instruction, MemArg, MemorySection, MemoryType, Module as WasmModule, NameMap,
    NameSection, TypeSection, ValType,
};

pub mod errors;
pub use errors::{humanize, self_verify};

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
    I32Load {
        offset: u64,
    },
    I32Store {
        offset: u64,
    },
    F32Load {
        offset: u64,
    },
    F32Store {
        offset: u64,
    },
    /// Call the function at the given global index (imports occupy the
    /// low indices). Used by the multi-module caller to invoke an import.
    Call(u32),
    /// Drop the top stack value — consumes a value exactly once.
    Drop,
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
    /// Linear memory, if the module declares one. Region-bearing modules
    /// have memory; pure cross-module boundary modules need none.
    pub memory: Option<Memory>,
    /// Function imports (the cross-module boundary), ahead of `funcs` in
    /// the function index space.
    pub imports: Vec<Import>,
    pub funcs: Vec<Func>,
    /// Per-local-function ownership annotations: `(local_func_index,
    /// param_kinds)`. Emitted as the `typedwasm.ownership` carrier;
    /// empty = no L7/L10 carrier.
    pub ownership: Vec<(usize, Vec<Ownership>)>,
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
        Op::Call(i) => Instruction::Call(i),
        Op::Drop => Instruction::Drop,
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

        let mut f = Function::new([]);
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
                instruction_byte_offset: site.offset,
                region_id: site.region as u32,
                field_id: site.field as u32,
            });
        }
    }

    // typedwasm.ownership carrier (L7/L10), keyed by GLOBAL function index.
    let ownership_entries: Vec<OwnershipEntry> = module
        .ownership
        .iter()
        .map(|(local_i, kinds)| OwnershipEntry {
            func_idx: import_count + *local_i as u32,
            param_kinds: kinds.iter().map(|o| o.to_kind()).collect(),
            ret_kind: OwnershipKind::Unrestricted,
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
    // Debug symbols: the wasm `name` section gives debuggers readable
    // function names (Phase 1 deliverable 5 / #129, first increment — the
    // offset -> source-line map awaits source spans from the #127 seam).
    if !module.funcs.is_empty() {
        let mut names = NameSection::new();
        let mut fnames = NameMap::new();
        for (local_i, func) in module.funcs.iter().enumerate() {
            fnames.append(import_count + local_i as u32, &func.name);
        }
        names.functions(&fnames);
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
    if !region_entries.is_empty() {
        let payload = build_regions_section_payload(&region_entries);
        wasm.section(&CustomSection {
            name: REGIONS_SECTION_NAME.into(),
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
        memory: Some(Memory {
            min_pages: 64,
            max_pages: Some(256),
        }),
        imports: vec![],
        funcs,
        ownership: vec![],
    }
}

/// Convenience: lower [`example01`] to wasm bytes.
pub fn emit_example01() -> Vec<u8> {
    emit(&example01())
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
            body: vec![Op::LocalGet(0), Op::Drop], // uses the Linear param once
            accesses: vec![],
            export: true,
        }],
        ownership: vec![(0, vec![Ownership::Linear])],
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
            body,
            accesses: vec![],
            export: false,
        }],
        ownership: vec![],
    }
}

/// Convenience: emit the `(callee, caller)` pair for the clean
/// single-call linear transfer.
pub fn emit_multimodule() -> (Vec<u8>, Vec<u8>) {
    (emit(&multimodule_callee()), emit(&multimodule_caller(1)))
}

// ----------------------------------------------------------------------
// example03: the IR for examples/03-ownership-linearity.twasm (#127)
// ----------------------------------------------------------------------

/// Build the IR for `examples/03-ownership-linearity.twasm` (L7–L10): a
/// `Particle` region plus functions exercising **Linear** (`own`),
/// **ExclBorrow** (`&mut`), and **SharedBorrow** (`&`) parameters, recorded
/// in the `typedwasm.ownership` carrier. Bodies use each owned/borrowed
/// parameter per the verifier's use-count discipline (Linear consumed
/// exactly once; ExclBorrow referenced at most once), so the module passes
/// `verify_from_module`.
pub fn example03() -> Module {
    let particle = Region {
        name: "Particle".into(),
        fields: vec![
            Field::scalar("pos_x", Scalar::F32),     // 0  (bytes 0..4)
            Field::scalar("pos_y", Scalar::F32),     // 1  (4..8)
            Field::scalar("vel_x", Scalar::F32),     // 2  (8..12)
            Field::scalar("vel_y", Scalar::F32),     // 3  (12..16)
            Field::scalar("lifetime", Scalar::F32),  // 4  (16..20)
            Field::scalar("colour", Scalar::U32),    // 5  (20..24)
            Field::scalar("is_alive", Scalar::Bool), // 6  (24)
        ],
        byte_size: 28,
    };

    let funcs = vec![
        // 0: despawn_particle(own Particle) — Linear, consumed exactly once.
        Func {
            name: "despawn_particle".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: vec![Op::LocalGet(0), Op::Drop],
            accesses: vec![],
            export: true,
        },
        // 1: update_particle(&mut Particle, dt) — ExclBorrow referenced once.
        Func {
            name: "update_particle".into(),
            params: vec![Wty::I32, Wty::F32],
            results: vec![],
            body: vec![Op::LocalGet(0), Op::F32Load { offset: 16 }, Op::Drop], // read .lifetime
            accesses: vec![AccessSite {
                region: 0,
                field: 4,
                offset: 6,
            }],
            export: true,
        },
        // 2: read_particle_pos(&Particle) -> f32 — SharedBorrow (unconstrained).
        Func {
            name: "read_particle_pos".into(),
            params: vec![Wty::I32],
            results: vec![Wty::F32],
            body: vec![Op::LocalGet(0), Op::F32Load { offset: 0 }], // read .pos_x
            accesses: vec![AccessSite {
                region: 0,
                field: 0,
                offset: 6,
            }],
            export: true,
        },
        // 3: spawn_particle(...) -> own handle — value params (Unrestricted).
        Func {
            name: "spawn_particle".into(),
            params: vec![Wty::F32, Wty::F32, Wty::F32, Wty::F32, Wty::F32, Wty::I32],
            results: vec![Wty::I32],
            body: vec![Op::I32Const(0)], // representative: returns a handle
            accesses: vec![],
            export: true,
        },
    ];

    Module {
        regions: vec![particle],
        memory: Some(Memory {
            min_pages: 16,
            max_pages: Some(64),
        }),
        imports: vec![],
        funcs,
        ownership: vec![
            (0, vec![Ownership::Linear]), // despawn: own
            (1, vec![Ownership::ExclBorrow, Ownership::Unrestricted]), // update: &mut, dt
            (2, vec![Ownership::SharedBorrow]), // read: &
        ],
    }
}

/// Convenience: lower [`example03`] to wasm bytes.
pub fn emit_example03() -> Vec<u8> {
    emit(&example03())
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
