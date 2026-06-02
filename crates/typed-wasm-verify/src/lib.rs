// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// typed-wasm post-codegen verifier.
//
// Statically verifies typed-wasm L7 (aliasing safety) and L10 (linearity)
// on emitted wasm modules. Reads the `typedwasm.ownership` custom
// section, then runs per-path min/max use-range analysis on every
// function body in the module.
//
// Rust port of hyperpolymath/affinescript:
//   - lib/tw_verify.ml    (intra-function verifier, ~246 lines OCaml)
//   - lib/tw_interface.ml (cross-module boundary verifier, ~245 lines OCaml)
//
// The OCaml files are the spec of record until this crate reaches
// behavioural parity (tracked by C5 in the workspace task list).

use thiserror::Error;

pub mod cross;
pub mod section;
pub mod verify;
pub use cross::{extract_exports, verify_cross_module};
pub use section::{
    build_ownership_section_payload, parse_ownership_section_payload, OwnershipEntry,
};
pub use verify::{count_uses_range, verify_function};

#[cfg(feature = "unstable-l2")]
pub use section::{
    build_regions_section_payload, parse_regions_section_payload, FieldEntry, FieldKind,
    Nullability, RegionEntry, WasmTy, REGIONS_SECTION_VERSION,
};

#[cfg(feature = "unstable-l13-imports")]
pub use section::{
    build_region_imports_section_payload, parse_region_imports_section_payload,
    ImportedFieldEntry, RegionImportEntry, IMPORT_TABLE_BASE, REGION_IMPORTS_SECTION_VERSION,
};

/// Ownership kinds matching the OCaml `Codegen.ownership_kind` enum.
/// Wire encoding in the `typedwasm.ownership` custom section: a single
/// u8 per kind, values 0/1/2/3 as below.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OwnershipKind {
    Unrestricted = 0,
    Linear = 1,
    SharedBorrow = 2,
    ExclBorrow = 3,
}

impl OwnershipKind {
    /// Decode a wire byte. Any value outside 0..=3 maps to `Unrestricted`
    /// — matches the OCaml `kind_of_byte` fallback.
    pub fn from_byte(b: u8) -> Self {
        match b {
            1 => OwnershipKind::Linear,
            2 => OwnershipKind::SharedBorrow,
            3 => OwnershipKind::ExclBorrow,
            _ => OwnershipKind::Unrestricted,
        }
    }

    /// Encode to the single-byte wire value.
    pub fn to_byte(self) -> u8 {
        self as u8
    }
}

/// An ownership violation found in a wasm function body.
/// Mirrors OCaml `Tw_verify.ownership_error`.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum OwnershipError {
    #[error("Level 10 violation: function {func_idx}, param {param_idx} — Linear (own) param dropped on all paths (must be consumed exactly once)")]
    LinearNotUsed { func_idx: u32, param_idx: u32 },

    #[error("Level 10 violation: function {func_idx}, param {param_idx} — Linear (own) param dropped on some paths (per-path min uses = 0; must be consumed on every path)")]
    LinearDroppedOnSomePath { func_idx: u32, param_idx: u32 },

    #[error("Level 10 violation: function {func_idx}, param {param_idx} — Linear (own) param loaded {count} times on some path (exactly 1 required; possible duplication)")]
    LinearUsedMultiple {
        func_idx: u32,
        param_idx: u32,
        count: u32,
    },

    #[error("Level 7 violation: function {func_idx}, param {param_idx} — ExclBorrow (mut) param aliased ({count} simultaneous references; at most 1 permitted)")]
    ExclBorrowAliased {
        func_idx: u32,
        param_idx: u32,
        count: u32,
    },

    /// Level 13 (module isolation, negative form). Mirrors OCaml
    /// `Tw_verify.ModuleNotIsolated` (affinescript PR #280, issue #35):
    /// the module owns its own linear memory yet also imports a memory
    /// or table — a cross-module shared-state channel outside the
    /// declared function-import boundary. Carrier-free (standard
    /// import/memory sections only; no ownership-section ABI change).
    #[error("Level 13 violation: {reason}")]
    ModuleNotIsolated { reason: String },
}

/// A cross-module ownership violation found in a caller's function body.
/// Mirrors OCaml `Tw_interface.cross_error`.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CrossError {
    #[error("Level 10 boundary violation: caller fn {caller_func_idx} calls import '{import_name}' {count} time(s) on some path (Linear param; must be called at most once)")]
    LinearImportCalledMultiple {
        caller_func_idx: u32,
        import_func_idx: u32,
        import_name: String,
        count: u32,
    },

    #[error("Level 10 boundary violation: caller fn {caller_func_idx} calls import '{import_name}' on some paths but not others (Linear param dropped on zero-call path)")]
    LinearImportDroppedOnSomePath {
        caller_func_idx: u32,
        import_func_idx: u32,
        import_name: String,
    },
}

/// Top-level verification failures (parse + verify).
#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("wasm parse error: {0}")]
    Parse(#[from] wasmparser::BinaryReaderError),

    #[error("ownership violations: {0:?}")]
    Ownership(Vec<OwnershipError>),

    #[error("cross-module boundary violations: {0:?}")]
    Cross(Vec<CrossError>),
}

/// Custom-section name carrying ownership annotations. Producer-neutral as
/// of the 2026-05-26 rename; both AffineScript (`Codegen.build_ownership_section`)
/// and Ephapax (`ephapax-wasm`) emit and read this name.
pub const OWNERSHIP_SECTION_NAME: &str = "typedwasm.ownership";

/// Custom-section name carrying L2–L6 region/field schema. Pre-staged
/// against typed-wasm proposal 0001 (typed-wasm#76, refs #34).
/// UNSTABLE: wire format may change before the proposal is [accepted].
#[cfg(feature = "unstable-l2")]
pub const REGIONS_SECTION_NAME: &str = "typedwasm.regions";

/// Custom-section name carrying L15 capability lattice (proposal 0001).
/// UNSTABLE.
#[cfg(feature = "unstable-l15")]
pub const CAPABILITIES_SECTION_NAME: &str = "typedwasm.capabilities";

/// Custom-section name carrying per-instruction `(region_id, field_id)`
/// mapping (proposal 0002, typed-wasm#86). UNSTABLE.
#[cfg(feature = "unstable-l2")]
pub const ACCESS_SITES_SECTION_NAME: &str = "typedwasm.access-sites";

/// Custom-section name carrying cross-module region-import declarations
/// (proposal 0003, typed-wasm#140 refs #95). Companion to
/// `typedwasm.regions`: a module's `target_region` foreign keys with the
/// import-table bit set (`>= IMPORT_TABLE_BASE`) resolve through this
/// section's entries. UNSTABLE.
#[cfg(feature = "unstable-l13-imports")]
pub const REGION_IMPORTS_SECTION_NAME: &str = "typedwasm.region-imports";

/// L15 capability-section violation (parsing succeeded, content invalid).
#[cfg(feature = "unstable-l15")]
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CapabilitiesError {
    #[error("Level 15 violation: function index {func_idx} (entry {entry_idx}) is out of bounds for wasm function section (function_count = {function_count})")]
    FuncIdxOutOfRange {
        entry_idx: u32,
        func_idx: u32,
        function_count: u32,
    },

    #[error("Level 15 violation: capability index {cap_idx} in function entry {entry_idx} (func_idx = {func_idx}) is out of bounds for capability table (capability_count = {capability_count})")]
    CapabilityIdxOutOfRange {
        entry_idx: u32,
        func_idx: u32,
        cap_idx: u32,
        capability_count: u32,
    },
}

/// L2 access-site-section violation.
#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum AccessSiteError {
    /// Hard error per proposal 0002 §"Producer obligations" #2: a module
    /// with a `typedwasm.access-sites` section must also have a
    /// `typedwasm.regions` section — the access-site entries reference
    /// `region_id` + `field_id` keys with nothing to resolve them
    /// against otherwise.
    #[error("Level 2 violation: typedwasm.access-sites section emitted without companion typedwasm.regions section (MissingDependentCarrier)")]
    MissingDependentRegions,

    #[error("Level 2 violation: access-site entry {entry_idx}: func_idx {func_idx} is out of bounds for wasm function section (function_count = {function_count})")]
    FuncIdxOutOfRange {
        entry_idx: u32,
        func_idx: u32,
        function_count: u32,
    },

    #[error("Level 2 violation: access-site entry {entry_idx}: region_id {region_id} is out of bounds for typedwasm.regions table (region_count = {region_count})")]
    RegionIdOutOfRange {
        entry_idx: u32,
        region_id: u32,
        region_count: u32,
    },

    #[error("Level 2 violation: access-site entry {entry_idx}: field_id {field_id} is out of bounds for region {region_id}'s field table (field_count = {field_count})")]
    FieldIdOutOfRange {
        entry_idx: u32,
        region_id: u32,
        field_id: u32,
        field_count: u32,
    },
}

/// L13 region-imports section violation. Self-consistency only; cross-
/// module schema-agreement (`SchemaSub expected actual`, `SchemaImportMismatch`)
/// belongs to a future `verify_link_graph` pass (proposal 0003 §"Open
/// questions" #4 default option a).
#[cfg(feature = "unstable-l13-imports")]
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum RegionImportsError {
    /// Proposal 0003 §"Producer obligations" #1: a module emitting
    /// `typedwasm.region-imports` MUST also emit `typedwasm.regions` (the
    /// import-table foreign keys in `typedwasm.regions`'s field entries
    /// would otherwise dangle).
    #[error("Level 13 violation: typedwasm.region-imports section emitted without companion typedwasm.regions section (MissingDependentCarrier)")]
    MissingDependentRegions,

    /// Inverse companion check: a `typedwasm.regions` field entry has a
    /// `target_region` value with the import-table bit set, but no
    /// `typedwasm.region-imports` section is present to resolve it
    /// against. Emitted at most once per module (further occurrences
    /// would spam).
    #[error("Level 13 violation: typedwasm.regions has target_region with import-table bit set (value {target_region:#010x}) but no typedwasm.region-imports section present to resolve it")]
    MissingDependentRegionImports { target_region: u32 },

    /// Proposal 0003 §"Wire format" Notes: imports MUST have unique
    /// `(producer_module_name, region_name)` pairs.
    #[error("Level 13 violation: duplicate import: (producer_module_name = {producer_module_name:?}, region_name = {region_name:?}) appears at import-table indices {first_idx} and {duplicate_idx}")]
    DuplicateImport {
        first_idx: u32,
        duplicate_idx: u32,
        producer_module_name: String,
        region_name: String,
    },

    /// Proposal 0003 §"Producer obligations" #5: imported regions MUST
    /// have scalar-only expected schemas in v1. Transitive pointer-chain
    /// resolution is deferred to v2 (see proposal 0003 §"Open questions" #1).
    #[error("Level 13 violation: import-table entry {import_idx}: expected field {field_idx} ({field_name:?}) has pointer kind {kind:?}; pointer fields are not supported in imported regions in v1 (proposal 0003 §Producer obligations 5)")]
    PointerInImportNotSupportedInV1 {
        import_idx: u32,
        field_idx: u32,
        field_name: String,
        kind: FieldKind,
    },

    /// A `typedwasm.regions` field entry has a `target_region` value
    /// with the import-table bit set, but the resolved index points past
    /// the end of the `typedwasm.region-imports` table.
    #[error("Level 13 violation: typedwasm.regions region {region_idx} field {field_idx}: target_region value {target_region:#010x} resolves to import-table index {resolved_idx} but only {import_count} imports are declared")]
    ImportTargetOutOfRange {
        region_idx: u32,
        field_idx: u32,
        target_region: u32,
        resolved_idx: u32,
        import_count: u32,
    },
}

// ----------------------------------------------------------------------
// Public entry points (stubbed in C1; implementations land in C2-C4).
// ----------------------------------------------------------------------

/// Verify the L7+L10 ownership constraints on a wasm module by reading its
/// embedded `typedwasm.ownership` custom section. Returns `Ok(())` when
/// no violations are found; modules without the section verify trivially.
///
/// Rust port of OCaml `Tw_verify.verify_from_module`.
pub fn verify_from_module(wasm_bytes: &[u8]) -> Result<(), VerifyError> {
    verify::verify_from_module(wasm_bytes)
}

/// Verify the L15 capability constraints on a wasm module by reading
/// its embedded `typedwasm.capabilities` custom section. Modules without
/// the section verify trivially. Checks:
///
/// 1. Every per-function `func_idx` is within the module's function
///    section bounds.
/// 2. Every per-function `required` capability index is within the
///    section's capability table bounds.
///
/// `DistinctCaps` (strictly-increasing per-function required list) is
/// not re-checked here because the codec parser already normalises
/// `required` to sorted+deduped form on read — verifying it would
/// require parsing the raw wire bytes pre-normalisation.
#[cfg(feature = "unstable-l15")]
pub fn verify_capabilities_from_module(
    wasm_bytes: &[u8],
) -> Result<Vec<CapabilitiesError>, VerifyError> {
    verify::verify_capabilities_from_module(wasm_bytes)
}

/// Verify the L2 access-site constraints on a wasm module by reading
/// its embedded `typedwasm.access-sites` + `typedwasm.regions` custom
/// sections. Returns `Ok(vec![])` when no violations are found; modules
/// without the access-sites section verify trivially. Checks:
///
/// 1. `MissingDependentCarrier`: access-sites present without regions
///    is a hard error (per proposal 0002 §"Producer obligations" #2).
/// 2. Every entry's `func_idx` is within the module's function section
///    bounds.
/// 3. Every entry's `region_id` is within the regions table.
/// 4. Every entry's `field_id` is within the target region's field
///    table.
///
/// Does NOT check `instruction_byte_offset` validity (would require
/// parsing function bodies to verify the offset lands on a typed
/// access opcode — proposal 0002 calls this `AccessSiteMisalignment`
/// and defers it to a follow-up).
#[cfg(feature = "unstable-l2")]
pub fn verify_access_sites_from_module(
    wasm_bytes: &[u8],
) -> Result<Vec<AccessSiteError>, VerifyError> {
    verify::verify_access_sites_from_module(wasm_bytes)
}

/// Verify the L13 region-imports section's in-module self-consistency by
/// reading its embedded `typedwasm.region-imports` and `typedwasm.regions`
/// custom sections. Modules emitting neither section verify trivially.
///
/// Checks:
///
/// 1. `MissingDependentRegions`: region-imports present without regions
///    is a hard error (proposal 0003 §"Producer obligations" #1).
/// 2. `MissingDependentRegionImports`: regions present with at least one
///    `target_region` value `>= IMPORT_TABLE_BASE` (i.e. claiming an
///    import) without region-imports is a hard error (emitted at most
///    once per module).
/// 3. `DuplicateImport`: imports MUST have unique
///    `(producer_module_name, region_name)` pairs.
/// 4. `PointerInImportNotSupportedInV1`: imported regions' expected
///    fields MUST all be `kind == Scalar` in v1.
/// 5. `ImportTargetOutOfRange`: every `target_region` value with the
///    import-table bit set MUST resolve within the import-table bounds.
///
/// Does NOT verify cross-module schema agreement (`SchemaSub expected
/// actual` from `MultiModule.idr`); that requires the producer module's
/// bytes and is the subject of a future `verify_link_graph(modules)` pass
/// (proposal 0003 §"Open questions" #4 default option a).
#[cfg(feature = "unstable-l13-imports")]
pub fn verify_region_imports_from_module(
    wasm_bytes: &[u8],
) -> Result<Vec<RegionImportsError>, VerifyError> {
    verify::verify_region_imports_from_module(wasm_bytes)
}

/// Ownership-annotated signature for one exported function.
/// Mirrors OCaml `Tw_interface.func_interface`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncInterface {
    pub name: String,
    pub func_idx: u32,
    pub param_kinds: Vec<OwnershipKind>,
    pub ret_kind: OwnershipKind,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ownership_kind_byte_roundtrip() {
        for (b, k) in [
            (0, OwnershipKind::Unrestricted),
            (1, OwnershipKind::Linear),
            (2, OwnershipKind::SharedBorrow),
            (3, OwnershipKind::ExclBorrow),
        ] {
            assert_eq!(OwnershipKind::from_byte(b), k);
        }
        assert_eq!(OwnershipKind::from_byte(99), OwnershipKind::Unrestricted);
    }
}
