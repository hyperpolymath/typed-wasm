// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! typed-wasm producer — **codegen v0**.
//!
//! The first in-tree `.twasm -> .wasm` producer. It lowers a typed region
//! [`Module`] IR to a well-formed wasm module plus the `typedwasm.*` carrier
//! sections (`ownership` L7/L10, `regions` L2–L6, `access-sites` L2),
//! emitted via `typed-wasm-verify`'s *own* carrier encoders so the bytes
//! cannot drift from the decoder the verifier runs. Output round-trips
//! through [`typed_wasm_verify::verify_from_module`] +
//! `verify_access_sites_from_module` in-process (see `tests/`).
//!
//! ## Real codegen (ported from the Zig `twasmc` reference, PR #136)
//!
//! Function bodies are lowered through a **layout engine** that computes real
//! field offsets, element strides, and alignment (including arrays and
//! **inline embedded regions** — e.g. `Players` slot stride = 48 B, with
//! `.pos.x` reaching into the embedded `@Vec2` at offset 16). Typed accesses
//! emit **real loads/stores at computed offsets**, addressed as
//! `base + index*stride (+ field offsets)`. Each region-handle parameter is
//! read **exactly once** into a base-pointer local (the `twasmc` convention),
//! so `&mut` (ExclBorrow) / `own` (Linear) handles never trip the verifier's
//! per-path use-count regardless of how many fields they touch.
//!
//! ## Deferred (see ADR-0004)
//!
//! * Front-end (`.twasm`) → IR seam: the IR is still hand-built per example
//!   (no in-process parser); tracked by #127.
//! * Full control flow: `if`/`else` and `region.scan` loops are simplified —
//!   bodies emit the real typed accesses but not the exact source branching.
//! * Source → line maps (#129, beyond the `name` section emitted here).

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

/// A scalar field storage type. Maps onto [`typed_wasm_verify::WasmTy`] for
/// the `typedwasm.regions` carrier and drives the layout engine's sizing.
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
    /// Storage size in bytes (also the natural alignment).
    fn size(self) -> u32 {
        match self {
            Scalar::I8 | Scalar::U8 | Scalar::Bool => 1,
            Scalar::I16 | Scalar::U16 => 2,
            Scalar::I32 | Scalar::U32 | Scalar::F32 => 4,
            Scalar::I64 | Scalar::U64 | Scalar::F64 => 8,
        }
    }

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

/// Pointer/reference kind for a region-typed field (`ptr<R>` / `opt<@R>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtrKind {
    Owning,
    Borrow,
    Exclusive,
}

/// A field's type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTy {
    /// A scalar value (size from [`Scalar::size`]; arrays via `cardinality`).
    Scalar(Scalar),
    /// An **inline embedded** region (`@R`) — contributes the target
    /// region's full stride to the layout (not a pointer).
    Embedded { region: usize },
    /// A pointer/handle to another region (`ptr<R>` / `opt<@R>`) — 4 bytes.
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
    pub fn embedded(name: &str, region: usize) -> Self {
        Field {
            name: name.into(),
            ty: FieldTy::Embedded { region },
            cardinality: 1,
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
    /// Declared minimum alignment (`align N`); 0 = natural (max field align).
    pub align: u32,
}

impl Region {
    pub fn new(name: &str, fields: Vec<Field>) -> Self {
        Region {
            name: name.into(),
            fields,
            align: 0,
        }
    }
    pub fn aligned(name: &str, fields: Vec<Field>, align: u32) -> Self {
        Region {
            name: name.into(),
            fields,
            align,
        }
    }
}

/// A wasm value type usable as a function parameter/result.
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

/// Low-level ops for non-region function bodies (the multi-module boundary
/// functions). Region accesses use [`Stmt`]/[`Access`] instead.
#[derive(Debug, Clone, Copy)]
pub enum Op {
    LocalGet(u32),
    /// Call the function at the given global index (imports occupy the low indices).
    Call(u32),
    /// Drop the top stack value — consumes a value exactly once.
    Drop,
}

/// Ownership discipline for a function parameter (`typedwasm.ownership`).
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

/// A function import (the cross-module boundary).
#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub field: String,
    pub params: Vec<Wty>,
    pub results: Vec<Wty>,
}

/// A typed field access: `region[index].path…`, resolving (via the layout
/// engine) to a leaf field at a computed byte offset.
#[derive(Debug, Clone)]
pub struct Access {
    /// Param index of the region base pointer (read once into a base local).
    pub handle: u32,
    /// Param index of the element index, or `None` for element 0 / a single region.
    pub index: Option<u32>,
    /// Region index (into [`Module::regions`]) the path starts in.
    pub region: usize,
    /// Field-index path; the final element resolves to a scalar/pointer leaf.
    pub path: Vec<usize>,
}

impl Access {
    /// `handle[index].field` (single field).
    pub fn field(handle: u32, index: Option<u32>, region: usize, field: usize) -> Self {
        Access {
            handle,
            index,
            region,
            path: vec![field],
        }
    }
    /// `handle[index].a.b` (nested path).
    pub fn nested(handle: u32, index: Option<u32>, region: usize, path: Vec<usize>) -> Self {
        Access {
            handle,
            index,
            region,
            path,
        }
    }
}

/// One statement in a typed function body.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// Load the access's leaf and leave it as the function result.
    Return(Access),
    /// Load the access's leaf and drop it (a read with no result).
    Read(Access),
    /// Store parameter `value` into the access's leaf.
    Set { access: Access, value: u32 },
    /// Return an `i32` constant (representative stand-in for not-yet-lowered
    /// control flow such as `region.scan`).
    ReturnConst(i32),
}

/// A function body: either low-level ops (boundary functions) or layout-driven
/// typed accesses (region functions).
#[derive(Debug, Clone)]
pub enum Body {
    Ops(Vec<Op>),
    /// `handles` are the region-handle params (each read once into a base
    /// local — ownership-clean); `stmts` are lowered through the layout engine.
    Typed {
        handles: Vec<u32>,
        stmts: Vec<Stmt>,
    },
}

/// A function: a typed signature, a body, and an export flag.
#[derive(Debug, Clone)]
pub struct Func {
    pub name: String,
    pub params: Vec<Wty>,
    pub results: Vec<Wty>,
    pub body: Body,
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
    pub memory: Option<Memory>,
    pub imports: Vec<Import>,
    pub funcs: Vec<Func>,
    /// Per-local-function ownership: `(local_func_index, param_kinds)`.
    pub ownership: Vec<(usize, Vec<Ownership>)>,
}

// ----------------------------------------------------------------------
// Layout engine — real field offsets / stride / alignment
// (ported from the Zig `twasmc` layout engine, PR #136)
// ----------------------------------------------------------------------

/// Computed memory layout of a region.
#[derive(Debug, Clone)]
struct RegionLayout {
    /// Byte offset of each field within one element.
    field_offsets: Vec<u32>,
    /// Element stride (size rounded up to the region's alignment).
    stride: u32,
    /// Region alignment (max of declared + natural field alignments).
    align: u32,
}

fn align_up(x: u32, a: u32) -> u32 {
    if a <= 1 {
        x
    } else {
        x.div_ceil(a) * a
    }
}

/// Compute the layout of `regions[idx]`, recursing into embedded regions.
fn region_layout(regions: &[Region], idx: usize) -> RegionLayout {
    let region = &regions[idx];
    let mut cursor: u32 = 0;
    let mut max_align: u32 = region.align.max(1);
    let mut field_offsets = Vec::with_capacity(region.fields.len());

    for f in &region.fields {
        let (size, align) = match f.ty {
            FieldTy::Scalar(s) => (s.size() * f.cardinality.max(1), s.size()),
            FieldTy::Embedded { region: r } => {
                let inner = region_layout(regions, r);
                (inner.stride, inner.align)
            }
            FieldTy::Ptr { .. } => (4, 4),
        };
        cursor = align_up(cursor, align);
        field_offsets.push(cursor);
        cursor += size;
        if align > max_align {
            max_align = align;
        }
    }

    RegionLayout {
        field_offsets,
        stride: align_up(cursor, max_align),
        align: max_align,
    }
}

/// The leaf a path resolves to (drives load/store opcode + width).
#[derive(Debug, Clone, Copy)]
enum Leaf {
    Scalar(Scalar),
    /// A pointer/handle leaf — loaded/stored as i32.
    Ptr,
}

/// Resolve `path` from `start_region`: returns the summed byte offset, the
/// leaf kind, and the leaf's `(region, field)` for the access-site carrier.
fn resolve_path(
    regions: &[Region],
    start_region: usize,
    path: &[usize],
) -> (u64, Leaf, usize, usize) {
    let mut cur = start_region;
    let mut off: u64 = 0;
    let mut leaf = Leaf::Ptr;
    let mut leaf_region = start_region;
    let mut leaf_field = 0usize;

    for (i, &fi) in path.iter().enumerate() {
        let lay = region_layout(regions, cur);
        off += lay.field_offsets[fi] as u64;
        leaf_region = cur;
        leaf_field = fi;
        match regions[cur].fields[fi].ty {
            FieldTy::Scalar(s) => leaf = Leaf::Scalar(s),
            FieldTy::Ptr { .. } => leaf = Leaf::Ptr,
            FieldTy::Embedded { region: r } => {
                if i + 1 < path.len() {
                    cur = r; // descend into the embedded region
                } else {
                    leaf = Leaf::Ptr; // embedded-as-leaf: treat the address as i32
                }
            }
        }
    }
    (off, leaf, leaf_region, leaf_field)
}

fn memarg(offset: u64, align: u32) -> MemArg {
    MemArg {
        offset,
        align,
        memory_index: 0,
    }
}

fn leaf_load(leaf: Leaf, off: u64) -> Instruction<'static> {
    match leaf {
        Leaf::Scalar(Scalar::Bool) | Leaf::Scalar(Scalar::U8) => {
            Instruction::I32Load8U(memarg(off, 0))
        }
        Leaf::Scalar(Scalar::I8) => Instruction::I32Load8S(memarg(off, 0)),
        Leaf::Scalar(Scalar::U16) => Instruction::I32Load16U(memarg(off, 1)),
        Leaf::Scalar(Scalar::I16) => Instruction::I32Load16S(memarg(off, 1)),
        Leaf::Scalar(Scalar::U32) | Leaf::Scalar(Scalar::I32) | Leaf::Ptr => {
            Instruction::I32Load(memarg(off, 2))
        }
        Leaf::Scalar(Scalar::U64) | Leaf::Scalar(Scalar::I64) => {
            Instruction::I64Load(memarg(off, 3))
        }
        Leaf::Scalar(Scalar::F32) => Instruction::F32Load(memarg(off, 2)),
        Leaf::Scalar(Scalar::F64) => Instruction::F64Load(memarg(off, 3)),
    }
}

fn leaf_store(leaf: Leaf, off: u64) -> Instruction<'static> {
    match leaf {
        Leaf::Scalar(Scalar::Bool) | Leaf::Scalar(Scalar::U8) | Leaf::Scalar(Scalar::I8) => {
            Instruction::I32Store8(memarg(off, 0))
        }
        Leaf::Scalar(Scalar::U16) | Leaf::Scalar(Scalar::I16) => {
            Instruction::I32Store16(memarg(off, 1))
        }
        Leaf::Scalar(Scalar::U32) | Leaf::Scalar(Scalar::I32) | Leaf::Ptr => {
            Instruction::I32Store(memarg(off, 2))
        }
        Leaf::Scalar(Scalar::U64) | Leaf::Scalar(Scalar::I64) => {
            Instruction::I64Store(memarg(off, 3))
        }
        Leaf::Scalar(Scalar::F32) => Instruction::F32Store(memarg(off, 2)),
        Leaf::Scalar(Scalar::F64) => Instruction::F64Store(memarg(off, 3)),
    }
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
        // The regions carrier has no "embedded" variant; an inline `@R` is
        // represented as an owning reference to the target region (the layout
        // engine treats it inline regardless).
        FieldTy::Embedded { region } => FieldEntry {
            name: f.name.clone(),
            kind: FieldKind::PtrOwning,
            wasm_ty: WasmTy::NotApplicable,
            target_region: region as u32,
            nullability: Nullability::NonNull,
            cardinality: 1,
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

/// Lower a [`Func`] body into `f`, returning the access sites it performs
/// (with the leaf `(region, field)` resolved via the layout engine).
fn lower_body(
    func: &Func,
    regions: &[Region],
    global_idx: u32,
) -> (Function, Vec<AccessSiteEntry>) {
    let mut access = Vec::new();
    match &func.body {
        Body::Ops(ops) => {
            let mut f = Function::new([]);
            for op in ops {
                f.instruction(&match *op {
                    Op::LocalGet(i) => Instruction::LocalGet(i),
                    Op::Call(i) => Instruction::Call(i),
                    Op::Drop => Instruction::Drop,
                });
            }
            f.instruction(&Instruction::End);
            (f, access)
        }
        Body::Typed { handles, stmts } => {
            let nparams = func.params.len() as u32;
            // One i32 base local per region handle.
            let locals: Vec<(u32, ValType)> = if handles.is_empty() {
                vec![]
            } else {
                vec![(handles.len() as u32, ValType::I32)]
            };
            let mut f = Function::new(locals);

            // Prologue: read each handle param exactly once into its base
            // local (the twasmc convention that keeps &mut/own bytes clean).
            let base_of =
                |h: u32| -> u32 { nparams + handles.iter().position(|&x| x == h).unwrap() as u32 };
            for &h in handles {
                f.instruction(&Instruction::LocalGet(h));
                f.instruction(&Instruction::LocalSet(base_of(h)));
            }

            let mut site_off: u32 = 0;
            let emit_addr = |f: &mut Function, a: &Access| {
                f.instruction(&Instruction::LocalGet(base_of(a.handle)));
                if let Some(ix) = a.index {
                    let stride = region_layout(regions, a.region).stride;
                    f.instruction(&Instruction::LocalGet(ix));
                    f.instruction(&Instruction::I32Const(stride as i32));
                    f.instruction(&Instruction::I32Mul);
                    f.instruction(&Instruction::I32Add);
                }
            };

            for stmt in stmts {
                match stmt {
                    Stmt::Return(a) | Stmt::Read(a) => {
                        let (off, leaf, lr, lf) = resolve_path(regions, a.region, &a.path);
                        emit_addr(&mut f, a);
                        f.instruction(&leaf_load(leaf, off));
                        if matches!(stmt, Stmt::Read(_)) {
                            f.instruction(&Instruction::Drop);
                        }
                        access.push(AccessSiteEntry {
                            func_idx: global_idx,
                            instruction_byte_offset: site_off,
                            region_id: lr as u32,
                            field_id: lf as u32,
                        });
                        site_off += 1;
                    }
                    Stmt::Set { access: a, value } => {
                        let (off, leaf, lr, lf) = resolve_path(regions, a.region, &a.path);
                        emit_addr(&mut f, a);
                        f.instruction(&Instruction::LocalGet(*value));
                        f.instruction(&leaf_store(leaf, off));
                        access.push(AccessSiteEntry {
                            func_idx: global_idx,
                            instruction_byte_offset: site_off,
                            region_id: lr as u32,
                            field_id: lf as u32,
                        });
                        site_off += 1;
                    }
                    Stmt::ReturnConst(c) => {
                        f.instruction(&Instruction::I32Const(*c));
                    }
                }
            }
            f.instruction(&Instruction::End);
            (f, access)
        }
    }
}

/// Lower a typed-wasm [`Module`] IR to a wasm binary with embedded
/// `typedwasm.*` carrier sections, each emitted only when non-empty.
///
/// Section order is canonical (Type, Import, Function, Memory, Export, Code,
/// then custom sections), so output passes a full validator. Imports occupy
/// the low function indices; a local function's global index is
/// `imports.len() + local_index`.
pub fn emit(module: &Module) -> Vec<u8> {
    let import_count = module.imports.len() as u32;

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
        let global_idx = import_count + local_i as u32;
        funcs.function(global_idx);

        let (f, sites) = lower_body(func, &module.regions, global_idx);
        code.function(&f);
        access_entries.extend(sites);

        if func.export {
            exports.export(&func.name, ExportKind::Func, global_idx);
        }
    }

    // Export the linear memory so a host (Wasmtime, JS) can read/write region data.
    if module.memory.is_some() {
        exports.export("memory", ExportKind::Memory, 0);
    }

    let ownership_entries: Vec<OwnershipEntry> = module
        .ownership
        .iter()
        .map(|(local_i, kinds)| OwnershipEntry {
            func_idx: import_count + *local_i as u32,
            param_kinds: kinds.iter().map(|o| o.to_kind()).collect(),
            ret_kind: OwnershipKind::Unrestricted,
        })
        .collect();

    let region_entries: Vec<RegionEntry> = module
        .regions
        .iter()
        .enumerate()
        .map(|(i, r)| RegionEntry {
            name: r.name.clone(),
            fields: r.fields.iter().map(field_to_entry).collect(),
            region_byte_size: region_layout(&module.regions, i).stride,
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
    // Debug symbols: the wasm `name` section (#129 first increment).
    if !module.funcs.is_empty() {
        let mut names = NameSection::new();
        let mut fnames = NameMap::new();
        for (local_i, func) in module.funcs.iter().enumerate() {
            fnames.append(import_count + local_i as u32, &func.name);
        }
        names.functions(&fnames);
        wasm.section(&names);
    }
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
// example01: examples/01-single-module.twasm — real codegen (L2–L7)
// ----------------------------------------------------------------------

/// Build the IR for `examples/01-single-module.twasm`. Bodies are real typed
/// accesses: indexed field loads/stores at layout-computed offsets, including
/// the nested `.pos.x` reach into the embedded `@Vec2`. Region handles carry
/// `&`/`&mut` ownership and are read once into base locals.
pub fn example01() -> Module {
    // Vec2=0, Players=1, Enemies=2. (`pos` is an INLINE embedded Vec2.)
    let vec2 = Region::new(
        "Vec2",
        vec![
            Field::scalar("x", Scalar::F32),
            Field::scalar("y", Scalar::F32),
        ],
    );
    let players = Region::aligned(
        "Players",
        vec![
            Field::scalar("hp", Scalar::I32),     // 0
            Field::scalar("speed", Scalar::F64),  // 1
            Field::embedded("pos", 0),            // 2 -> inline Vec2
            Field::array("name", Scalar::U8, 24), // 3
        ],
        8,
    );
    let enemies = Region::new(
        "Enemies",
        vec![
            Field::scalar("hp", Scalar::I32),               // 0
            Field::scalar("damage", Scalar::I32),           // 1
            Field::ptr("target", PtrKind::Borrow, 1, true), // 2 -> opt<@Players>
            Field::embedded("pos", 0),                      // 3 -> inline Vec2
            Field::scalar("is_active", Scalar::Bool),       // 4
        ],
    );

    let funcs = vec![
        // get_player_hp(&Players, idx) -> i32 : returns Players[idx].hp
        Func {
            name: "get_player_hp".into(),
            params: vec![Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![Stmt::Return(Access::field(0, Some(1), 1, 0))],
            },
            export: true,
        },
        // damage_player(&mut Players, idx, amount) : Players[idx].hp = amount
        Func {
            name: "damage_player".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![Stmt::Set {
                    access: Access::field(0, Some(1), 1, 0),
                    value: 2,
                }],
            },
            export: true,
        },
        // get_enemy_target_hp(&Enemies, &Players, idx) -> i32
        //   reads Enemies[idx].target then returns Players[idx].hp
        Func {
            name: "get_enemy_target_hp".into(),
            params: vec![Wty::I32, Wty::I32, Wty::I32],
            results: vec![Wty::I32],
            body: Body::Typed {
                handles: vec![0, 1],
                stmts: vec![
                    Stmt::Read(Access::field(0, Some(2), 2, 2)), // Enemies[idx].target
                    Stmt::Return(Access::field(1, Some(2), 1, 0)), // Players[idx].hp
                ],
            },
            export: true,
        },
        // count_active_enemies(&Enemies) -> i32 : reads is_active (scan simplified)
        Func {
            name: "count_active_enemies".into(),
            params: vec![Wty::I32],
            results: vec![Wty::I32],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![
                    Stmt::Read(Access::field(0, None, 2, 4)), // Enemies[0].is_active
                    Stmt::ReturnConst(0),
                ],
            },
            export: true,
        },
        // move_player(&mut Players, idx, dx, dy) : nested .pos.x / .pos.y writes
        Func {
            name: "move_player".into(),
            params: vec![Wty::I32, Wty::I32, Wty::F32, Wty::F32],
            results: vec![],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![
                    Stmt::Set {
                        access: Access::nested(0, Some(1), 1, vec![2, 0]),
                        value: 2,
                    }, // .pos.x = dx
                    Stmt::Set {
                        access: Access::nested(0, Some(1), 1, vec![2, 1]),
                        value: 3,
                    }, // .pos.y = dy
                ],
            },
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
        ownership: vec![
            (0, vec![Ownership::SharedBorrow, Ownership::Unrestricted]), // get_player_hp: &
            (
                1,
                vec![
                    Ownership::ExclBorrow,
                    Ownership::Unrestricted,
                    Ownership::Unrestricted,
                ],
            ), // damage: &mut
            (
                2,
                vec![
                    Ownership::SharedBorrow,
                    Ownership::SharedBorrow,
                    Ownership::Unrestricted,
                ],
            ), // &, &
            (3, vec![Ownership::SharedBorrow]),                          // count: &
            (
                4,
                vec![
                    Ownership::ExclBorrow,
                    Ownership::Unrestricted,
                    Ownership::Unrestricted,
                    Ownership::Unrestricted,
                ],
            ), // move: &mut
        ],
    }
}

/// Convenience: lower [`example01`] to wasm bytes.
pub fn emit_example01() -> Vec<u8> {
    emit(&example01())
}

// ----------------------------------------------------------------------
// Multi-module codegen — Phase 1 deliverable 7 (#128)
// ----------------------------------------------------------------------

/// Callee: exports a Linear `consume` (consumed once) + `typedwasm.ownership`.
pub fn multimodule_callee() -> Module {
    Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "consume".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: Body::Ops(vec![Op::LocalGet(0), Op::Drop]),
            export: true,
        }],
        ownership: vec![(0, vec![Ownership::Linear])],
    }
}

/// Caller importing `consume` and calling it `call_count` times.
pub fn multimodule_caller(call_count: u32) -> Module {
    let mut body = Vec::new();
    for _ in 0..call_count {
        body.push(Op::LocalGet(0));
        body.push(Op::Call(0)); // the import is global function index 0
    }
    Module {
        regions: vec![],
        memory: None,
        imports: vec![Import {
            module: "callee".into(),
            field: "consume".into(),
            params: vec![Wty::I32],
            results: vec![],
        }],
        funcs: vec![Func {
            name: "use_resource".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: Body::Ops(body),
            export: false,
        }],
        ownership: vec![],
    }
}

/// Convenience: the `(callee, caller)` pair for the clean single-call transfer.
pub fn emit_multimodule() -> (Vec<u8>, Vec<u8>) {
    (emit(&multimodule_callee()), emit(&multimodule_caller(1)))
}

// ----------------------------------------------------------------------
// example03: examples/03-ownership-linearity.twasm — L7–L10
// ----------------------------------------------------------------------

/// Build the IR for `examples/03-ownership-linearity.twasm`: a `Particle`
/// region + `own`/`&mut`/`&` functions emitting `typedwasm.ownership`, with
/// real field reads/writes at computed offsets. Each handle is read once into
/// a base local, so Linear/ExclBorrow params stay clean.
pub fn example03() -> Module {
    let particle = Region::aligned(
        "Particle",
        vec![
            Field::scalar("pos_x", Scalar::F32),     // 0 @0
            Field::scalar("pos_y", Scalar::F32),     // 1 @4
            Field::scalar("vel_x", Scalar::F32),     // 2 @8
            Field::scalar("vel_y", Scalar::F32),     // 3 @12
            Field::scalar("lifetime", Scalar::F32),  // 4 @16
            Field::scalar("colour", Scalar::U32),    // 5 @20
            Field::scalar("is_alive", Scalar::Bool), // 6 @24
        ],
        4,
    );

    let funcs = vec![
        // despawn_particle(own Particle) : consumed once (prologue read).
        Func {
            name: "despawn_particle".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![],
            },
            export: true,
        },
        // update_particle(&mut Particle, dt) : reads .lifetime.
        Func {
            name: "update_particle".into(),
            params: vec![Wty::I32, Wty::F32],
            results: vec![],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![Stmt::Read(Access::field(0, None, 0, 4))],
            },
            export: true,
        },
        // read_particle_pos(&Particle) -> f32 : returns .pos_x.
        Func {
            name: "read_particle_pos".into(),
            params: vec![Wty::I32],
            results: vec![Wty::F32],
            body: Body::Typed {
                handles: vec![0],
                stmts: vec![Stmt::Return(Access::field(0, None, 0, 0))],
            },
            export: true,
        },
        // spawn_particle(...) -> handle : value params; representative return.
        Func {
            name: "spawn_particle".into(),
            params: vec![Wty::F32, Wty::F32, Wty::F32, Wty::F32, Wty::F32, Wty::I32],
            results: vec![Wty::I32],
            body: Body::Typed {
                handles: vec![],
                stmts: vec![Stmt::ReturnConst(0)],
            },
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
            (1, vec![Ownership::ExclBorrow, Ownership::Unrestricted]), // update: &mut
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

/// Render a wasm binary to WAT (text) for debugging.
///
/// # Panics
/// Panics only if `wasm_bytes` is not well-formed wasm. [`emit`] always
/// produces well-formed wasm, so this never panics on emitter output.
pub fn wat(wasm_bytes: &[u8]) -> String {
    wasmprinter::print_bytes(wasm_bytes).expect("emitted wasm is well-formed and prints to WAT")
}

/// Lower a [`Module`] to WAT (text wasm).
pub fn emit_wat(module: &Module) -> String {
    wat(&emit(module))
}

/// Convenience: WAT for [`example01`].
pub fn emit_example01_wat() -> String {
    emit_wat(&example01())
}
