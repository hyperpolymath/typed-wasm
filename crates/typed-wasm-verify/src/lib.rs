// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// typed-wasm post-codegen verifier.
//
// Statically verifies typed-wasm L7 (aliasing safety) and L10 (linearity)
// on emitted wasm modules. Reads the `typedwasm.ownership` custom
// section, then runs per-path min/max use-range analysis on every
// function body in the module.
//
// SPEC OF RECORD (ADR-0008): this crate, with the formal statement in
// src/abi/TypedWasm/ABI/VerifierSpec.idr (+ MultiModule.idr for the
// cross-module layer). Historically a Rust port of affinescript's
// lib/tw_verify.ml / lib/tw_interface.ml — those OCaml files are now a
// conforming implementation, pinned by the cross_compat parity suites.

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
    Nullability, RegionEntry, WasmTy, ACCESS_SITE_UNPINNED, REGIONS_SECTION_VERSION,
};
#[cfg(feature = "unstable-l13-imports")]
pub use section::{
    build_region_imports_section_payload, parse_region_imports_section_payload,
    RegionImportEntry, REGION_IMPORTS_SECTION_VERSION,
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

/// Custom-section name for the L13 positive-form cross-module region
/// import table (proposal 0003 / ADR-0007).
#[cfg(feature = "unstable-l13-imports")]
pub const REGION_IMPORTS_SECTION_NAME: &str = "typedwasm.region-imports";

/// L13 region-imports violation (proposal 0003 §Consumer obligations).
#[cfg(feature = "unstable-l13-imports")]
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum RegionImportsError {
    /// `typedwasm.region-imports` present but `typedwasm.regions` absent
    /// or unparseable — the import table's foreign keys dangle.
    #[error("Level 13 violation: typedwasm.region-imports present without a parseable typedwasm.regions section (MissingDependentCarrier)")]
    MissingDependentRegions,

    /// The section is present but its version is unsupported / payload
    /// unparseable by this verifier.
    #[error("Level 13: typedwasm.region-imports section present but not parseable as version {expected} (unsupported carrier version or malformed payload)", expected = section::REGION_IMPORTS_SECTION_VERSION)]
    UnparseableSection,

    /// Duplicate `(producer_module, region_name)` pair — a producer bug.
    #[error("Level 13 violation: duplicate import of region '{region_name}' from module '{producer_module}' (import-table entries must be unique per (producer, region) pair)")]
    DuplicateImport {
        producer_module: String,
        region_name: String,
    },

    /// v1 restriction: expected schemas are scalar-only.
    #[error("Level 13 violation: import {import_idx} field '{field_name}' is pointer-typed — pointer fields in imported region schemas are not supported in v1 (proposal 0003 §Open Questions #1)")]
    PointerInImportNotSupportedInV1 {
        import_idx: u32,
        field_name: String,
    },

    /// A `target_region` high-bit foreign key in `typedwasm.regions`
    /// points past the import table.
    #[error("Level 13 violation: region {local_region_idx} field {field_idx} has target_region import-key {import_idx}, out of bounds for the import table (import_count = {import_count})")]
    ImportTargetOutOfRange {
        local_region_idx: u32,
        field_idx: u32,
        import_idx: u32,
        import_count: u32,
    },

    /// Link graph: no module with the named wasm module name.
    #[error("Level 13 violation: consumer '{consumer}' imports from producer module '{producer_module}', which is not present in the link graph")]
    UnresolvedProducerModule {
        consumer: String,
        producer_module: String,
    },

    /// Link graph: the producer exists but exports no such region.
    #[error("Level 13 violation: producer '{producer_module}' has no region named '{region_name}' in its typedwasm.regions table (imported by '{consumer}')")]
    UnresolvedExportedRegion {
        consumer: String,
        producer_module: String,
        region_name: String,
    },

    /// Link graph: the producer's actual exported schema does not
    /// satisfy the importer's expected schema (`SchemaSub` fails —
    /// `noSpoofing`, MultiModule.idr).
    #[error("Level 13 violation: schema mismatch importing '{region_name}' from '{producer_module}' into '{consumer}': missing fields {missing_fields:?}; type mismatches {type_mismatches:?}")]
    SchemaImportMismatch {
        consumer: String,
        producer_module: String,
        region_name: String,
        missing_fields: Vec<String>,
        type_mismatches: Vec<String>,
    },
}

/// A verified cross-module import: `consumer`'s expected schema for
/// `region_name` is satisfied by `producer`'s actual export. The wire
/// realisation of `MultiModule.idr::CompatCertificate`.
#[cfg(feature = "unstable-l13-imports")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompatCertificate {
    pub consumer: String,
    pub producer: String,
    pub region_name: String,
}

/// Result of a whole-link-graph L13 pass: one certificate per resolved
/// import, plus every violation found. Agreement holds iff
/// `errors.is_empty()`.
#[cfg(feature = "unstable-l13-imports")]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LinkGraphReport {
    pub certificates: Vec<CompatCertificate>,
    pub errors: Vec<RegionImportsError>,
}

/// Verify the internal consistency of a module's
/// `typedwasm.region-imports` section: dependent regions carrier
/// present, unique `(producer, region)` pairs, v1 scalar-only expected
/// schemas, and high-bit `target_region` foreign keys within the import
/// table. Modules without the section verify trivially. Cross-module
/// schema agreement is [`verify_link_graph`]'s job.
#[cfg(feature = "unstable-l13-imports")]
pub fn verify_region_imports_from_module(
    wasm_bytes: &[u8],
) -> Result<Vec<RegionImportsError>, VerifyError> {
    verify::verify_region_imports_from_module(wasm_bytes).map(|(_, errs)| errs)
}

/// Verify L13 positive-form schema agreement across a link graph of
/// `(wasm_module_name, wasm_bytes)` pairs: every region import in every
/// module must resolve to a producer in the graph whose actual exported
/// schema satisfies the importer's expected schema (`SchemaSub` —
/// every expected field present in the actual schema with matching
/// name, kind, type, nullability, and cardinality). Subset imports are
/// sound: importing 5 of 12 fields is agreement on those 5.
#[cfg(feature = "unstable-l13-imports")]
pub fn verify_link_graph(
    modules: &[(&str, &[u8])],
) -> Result<LinkGraphReport, VerifyError> {
    verify::verify_link_graph(modules)
}

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

/// L2 access-*typing* violation — the deep per-site check that decodes
/// the function body and confirms a pinned access lands on a load/store
/// of the target field's exact type, width, and offset, in-region.
/// This is the obligation proposal 0002 deferred as
/// `AccessSiteMisalignment`; here it is discharged at decode time.
///
/// Bounds errors (func/region/field id out of range) are the province of
/// [`AccessSiteError`]; this enum assumes a resolvable entry and reports
/// only the typing-layer faults. An entry that cannot be resolved is
/// reported as [`AccessTypingError::UnresolvableEntry`] and skipped.
#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum AccessTypingError {
    /// The entry's func/region/field id is out of range, or the pinned
    /// function is an import with no body — the typing pass cannot resolve
    /// what to check. (The bounds detail is [`AccessSiteError`]'s job.)
    #[error("Level 2 access-typing: entry {entry_idx} is unresolvable for typing ({reason})")]
    UnresolvableEntry { entry_idx: u32, reason: String },

    /// The pinned instruction index is past the end of the function's
    /// operator stream.
    #[error("Level 2 access-typing: entry {entry_idx} (func {func_idx}) pins instruction index {instruction_index}, but the body has only {op_count} operators")]
    AccessSiteIndexOutOfRange {
        entry_idx: u32,
        func_idx: u32,
        instruction_index: u32,
        op_count: u32,
    },

    /// The pinned instruction is not a memory load/store at all.
    #[error("Level 2 access-typing: entry {entry_idx} (func {func_idx}) pins instruction index {instruction_index}, which is `{found}` — not a typed memory load/store")]
    AccessSiteNotAMemoryOp {
        entry_idx: u32,
        func_idx: u32,
        instruction_index: u32,
        found: String,
    },

    /// The pinned instruction is a memory op, but of the wrong width/type
    /// for the field it claims to access (e.g. `i32.load` into a `u8`
    /// field, or `i64.store` into an `f64` field).
    #[error("Level 2 access-typing: entry {entry_idx}: field {region_id}.{field_id} has type {expected}, but the pinned instruction is `{found}`")]
    AccessTypeMismatch {
        entry_idx: u32,
        region_id: u32,
        field_id: u32,
        expected: String,
        found: String,
    },

    /// The memory op's static offset immediate does not equal the field's
    /// computed byte offset within its region.
    #[error("Level 2 access-typing: entry {entry_idx}: field {region_id}.{field_id} is at byte offset {expected_offset}, but the pinned instruction uses memarg offset {found_offset}")]
    AccessOffsetMismatch {
        entry_idx: u32,
        region_id: u32,
        field_id: u32,
        expected_offset: u32,
        found_offset: u64,
    },

    /// The field's `[offset, offset+width)` extent runs past the
    /// producer-declared region byte size.
    #[error("Level 2 access-typing: entry {entry_idx}: field {region_id}.{field_id} spans bytes [{field_offset}, {field_offset}+{field_width}) which exceeds region byte size {region_byte_size}")]
    AccessOutOfRegionBounds {
        entry_idx: u32,
        region_id: u32,
        field_id: u32,
        field_offset: u32,
        field_width: u32,
        region_byte_size: u32,
    },
}

/// The outcome of the L2 access-typing pass. `type_verified` and
/// `declared_only` partition the access sites the pass examined;
/// `errors` is empty iff every pinned site type-checked. This is the
/// "knowable what was actually checked" artifact: a caller (or
/// `tw-verify`) can report `N type-verified, M declared-only` so a
/// reader knows which sites carry a machine-checked typing guarantee and
/// which are merely asserted by the producer.
#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AccessTypingReport {
    /// Pinned sites whose pinned instruction matched the field's
    /// type/width/offset and stayed in-region — machine-checked.
    pub type_verified: u32,
    /// Sites the producer carried as declared-only (unpinned): asserted,
    /// not checked here.
    pub declared_only: u32,
    /// Typing faults found among the pinned sites.
    pub errors: Vec<AccessTypingError>,
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

/// Verify the L2 access-*typing* constraints: for every pinned
/// access-site, decode the function body, take the pinned instruction,
/// and confirm it is a memory load/store of the target field's exact
/// type and width, whose static offset equals the field's byte offset,
/// and whose extent stays within the region. Declared-only (unpinned)
/// sites are counted but not checked.
///
/// Returns an [`AccessTypingReport`]; `report.errors.is_empty()` iff
/// every pinned site type-checked. Modules without an access-sites
/// section return an empty report (nothing claimed). This is strictly
/// deeper than [`verify_access_sites_from_module`], which checks only
/// that the id fields are in range and never decodes the code section —
/// run both: bounds first, then typing.
#[cfg(feature = "unstable-l2")]
pub fn verify_access_typing_from_module(
    wasm_bytes: &[u8],
) -> Result<AccessTypingReport, VerifyError> {
    verify::verify_access_typing_from_module(wasm_bytes)
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
