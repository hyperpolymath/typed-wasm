// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// L13 positive-form cross-module region imports (proposal 0003 /
// ADR-0007, issue #140): the `typedwasm.region-imports` carrier +
// `verify_link_graph` realise MultiModule.idr's ImportedRegion /
// SchemaSub / noSpoofing on emitted bytes. Fixtures mirror
// examples/02-multi-module.twasm: `physics` exports Entity; `ai` and
// `render` import overlapping subsets of its schema.
#![cfg(feature = "unstable-l13-imports")]

use typed_wasm_verify::{
    build_region_imports_section_payload, build_regions_section_payload,
    verify_link_graph, verify_region_imports_from_module, FieldEntry, FieldKind, Nullability,
    RegionEntry, RegionImportEntry, RegionImportsError, WasmTy,
};
use wasm_encoder::{CustomSection, Module};

fn scalar(name: &str, ty: WasmTy, cardinality: u32) -> FieldEntry {
    FieldEntry {
        name: name.into(),
        kind: FieldKind::Scalar,
        wasm_ty: ty,
        target_region: typed_wasm_verify::section::NO_TARGET_REGION,
        nullability: Nullability::NonNull,
        cardinality,
    }
}

/// Module A of example-02: defines + exports Entity (subset of its 12
/// fields, enough for both importers' expectations).
fn entity_region() -> RegionEntry {
    RegionEntry {
        name: "Entity".into(),
        fields: vec![
            scalar("pos_x", WasmTy::F32, 1),
            scalar("pos_y", WasmTy::F32, 1),
            scalar("pos_z", WasmTy::F32, 1),
            scalar("scale", WasmTy::F32, 1),
            scalar("vel_x", WasmTy::F32, 1),
            scalar("vel_y", WasmTy::F32, 1),
            scalar("vel_z", WasmTy::F32, 1),
            scalar("mass", WasmTy::F32, 1),
            scalar("flags", WasmTy::U32, 1),
            scalar("friction", WasmTy::F32, 1),
            scalar("restitution", WasmTy::F32, 1),
            scalar("_reserved", WasmTy::U8, 4),
        ],
        region_byte_size: 48,
    }
}

/// Assemble a minimal wasm module (magic + version + custom sections).
fn module_with(
    regions: Option<&[RegionEntry]>,
    imports: Option<&[RegionImportEntry]>,
) -> Vec<u8> {
    let mut m = Module::new();
    if let Some(regions) = regions {
        let payload = build_regions_section_payload(regions);
        m.section(&CustomSection {
            name: "typedwasm.regions".into(),
            data: payload.as_slice().into(),
        });
    }
    if let Some(imports) = imports {
        let payload = build_region_imports_section_payload(imports);
        m.section(&CustomSection {
            name: "typedwasm.region-imports".into(),
            data: payload.as_slice().into(),
        });
    }
    m.finish()
}

fn ai_expected() -> Vec<FieldEntry> {
    vec![
        scalar("pos_x", WasmTy::F32, 1),
        scalar("pos_y", WasmTy::F32, 1),
        scalar("pos_z", WasmTy::F32, 1),
        scalar("vel_x", WasmTy::F32, 1),
        scalar("vel_y", WasmTy::F32, 1),
        scalar("vel_z", WasmTy::F32, 1),
        scalar("flags", WasmTy::U32, 1),
    ]
}

fn render_expected() -> Vec<FieldEntry> {
    vec![
        scalar("pos_x", WasmTy::F32, 1),
        scalar("pos_y", WasmTy::F32, 1),
        scalar("pos_z", WasmTy::F32, 1),
        scalar("scale", WasmTy::F32, 1),
        scalar("flags", WasmTy::U32, 1),
    ]
}

fn entity_import(expected: Vec<FieldEntry>) -> RegionImportEntry {
    RegionImportEntry {
        producer_module: "physics".into(),
        region_name: "Entity".into(),
        expected_fields: expected,
    }
}

fn ai_own_region() -> RegionEntry {
    RegionEntry {
        name: "AIState".into(),
        fields: vec![
            scalar("entity_idx", WasmTy::I32, 1),
            scalar("state", WasmTy::U8, 1),
            scalar("alert_level", WasmTy::F32, 1),
        ],
        region_byte_size: 12,
    }
}

/// The example-02 happy path: both importers' subset expectations are
/// satisfied by the producer's actual export — two certificates, no
/// errors. Subset imports (render takes 5 of 12 fields) are agreement.
#[test]
fn example02_link_graph_agrees() {
    let physics = module_with(Some(&[entity_region()]), None);
    let ai = module_with(
        Some(&[ai_own_region()]),
        Some(&[entity_import(ai_expected())]),
    );
    let render = module_with(
        Some(&[ai_own_region()]),
        Some(&[entity_import(render_expected())]),
    );

    let report = verify_link_graph(&[
        ("physics", physics.as_slice()),
        ("ai", ai.as_slice()),
        ("render", render.as_slice()),
    ])
    .expect("wasm parses");

    assert_eq!(report.errors, vec![], "clean graph must have no errors");
    assert_eq!(report.certificates.len(), 2);
    assert!(report
        .certificates
        .iter()
        .any(|c| c.consumer == "ai" && c.producer == "physics" && c.region_name == "Entity"));
    assert!(report.certificates.iter().any(|c| c.consumer == "render"));
}

/// noSpoofing teeth: an importer expecting `pos_x: f64` against the
/// producer's actual `f32` must be rejected with a type mismatch.
#[test]
fn type_mismatch_is_schema_import_mismatch() {
    let physics = module_with(Some(&[entity_region()]), None);
    let mut expected = ai_expected();
    expected[0].wasm_ty = WasmTy::F64;
    let ai = module_with(Some(&[ai_own_region()]), Some(&[entity_import(expected)]));

    let report =
        verify_link_graph(&[("physics", physics.as_slice()), ("ai", ai.as_slice())]).unwrap();
    assert_eq!(report.certificates, vec![]);
    match &report.errors[..] {
        [RegionImportsError::SchemaImportMismatch {
            type_mismatches,
            missing_fields,
            ..
        }] => {
            assert_eq!(missing_fields, &Vec::<String>::new());
            assert_eq!(type_mismatches.len(), 1);
            assert!(type_mismatches[0].starts_with("pos_x"));
        }
        other => panic!("expected one SchemaImportMismatch, got {other:?}"),
    }
}

/// Expecting a field the producer never exported → missing_fields.
#[test]
fn missing_field_is_schema_import_mismatch() {
    let physics = module_with(Some(&[entity_region()]), None);
    let mut expected = render_expected();
    expected.push(scalar("momentum", WasmTy::F32, 1));
    let render = module_with(Some(&[ai_own_region()]), Some(&[entity_import(expected)]));

    let report =
        verify_link_graph(&[("physics", physics.as_slice()), ("render", render.as_slice())])
            .unwrap();
    match &report.errors[..] {
        [RegionImportsError::SchemaImportMismatch { missing_fields, .. }] => {
            assert_eq!(missing_fields, &vec!["momentum".to_string()]);
        }
        other => panic!("expected one SchemaImportMismatch, got {other:?}"),
    }
}

/// A consumer whose named producer is not in the graph.
#[test]
fn absent_producer_is_unresolved_producer_module() {
    let ai = module_with(
        Some(&[ai_own_region()]),
        Some(&[entity_import(ai_expected())]),
    );
    let report = verify_link_graph(&[("ai", ai.as_slice())]).unwrap();
    assert!(matches!(
        &report.errors[..],
        [RegionImportsError::UnresolvedProducerModule { producer_module, .. }]
            if producer_module == "physics"
    ));
}

/// The producer exists but exports no region by that name.
#[test]
fn absent_region_is_unresolved_exported_region() {
    let mut renamed = entity_region();
    renamed.name = "Body".into();
    let physics = module_with(Some(&[renamed]), None);
    let ai = module_with(
        Some(&[ai_own_region()]),
        Some(&[entity_import(ai_expected())]),
    );
    let report =
        verify_link_graph(&[("physics", physics.as_slice()), ("ai", ai.as_slice())]).unwrap();
    assert!(matches!(
        &report.errors[..],
        [RegionImportsError::UnresolvedExportedRegion { region_name, .. }]
            if region_name == "Entity"
    ));
}

/// Producer-obligation violations caught module-locally.
#[test]
fn duplicate_import_pair_is_rejected() {
    let ai = module_with(
        Some(&[ai_own_region()]),
        Some(&[
            entity_import(ai_expected()),
            entity_import(render_expected()),
        ]),
    );
    let errs = verify_region_imports_from_module(&ai).unwrap();
    assert!(errs
        .iter()
        .any(|e| matches!(e, RegionImportsError::DuplicateImport { .. })));
}

#[test]
fn imports_without_regions_is_missing_dependent_carrier() {
    let ai = module_with(None, Some(&[entity_import(ai_expected())]));
    let errs = verify_region_imports_from_module(&ai).unwrap();
    assert_eq!(errs, vec![RegionImportsError::MissingDependentRegions]);
}

#[test]
fn pointer_expected_field_is_rejected_in_v1() {
    let mut expected = ai_expected();
    expected[0].kind = FieldKind::PtrBorrow;
    let ai = module_with(Some(&[ai_own_region()]), Some(&[entity_import(expected)]));
    let errs = verify_region_imports_from_module(&ai).unwrap();
    assert!(matches!(
        &errs[..],
        [RegionImportsError::PointerInImportNotSupportedInV1 { field_name, .. }]
            if field_name == "pos_x"
    ));
}

/// High-bit target_region foreign keys must land inside the import table.
#[test]
fn high_bit_foreign_key_past_import_table_is_rejected() {
    let mut own = ai_own_region();
    own.fields[0].kind = FieldKind::PtrBorrow;
    own.fields[0].wasm_ty = WasmTy::NotApplicable;
    own.fields[0].target_region = 0x8000_0000 + 5; // import #5 of a 1-entry table
    let ai = module_with(Some(&[own]), Some(&[entity_import(ai_expected())]));
    let errs = verify_region_imports_from_module(&ai).unwrap();
    assert!(matches!(
        &errs[..],
        [RegionImportsError::ImportTargetOutOfRange {
            import_idx: 5,
            import_count: 1,
            ..
        }]
    ));
}

/// In-range high-bit foreign keys are accepted (the v1.1 value-space
/// extension is non-breaking for import-aware consumers).
#[test]
fn high_bit_foreign_key_in_range_is_clean() {
    let mut own = ai_own_region();
    own.fields[0].kind = FieldKind::PtrBorrow;
    own.fields[0].wasm_ty = WasmTy::NotApplicable;
    own.fields[0].target_region = 0x8000_0000; // import #0
    let ai = module_with(Some(&[own]), Some(&[entity_import(ai_expected())]));
    let errs = verify_region_imports_from_module(&ai).unwrap();
    assert_eq!(errs, vec![]);
}

/// No section → trivially clean, no certificates claimed.
#[test]
fn absent_section_verifies_trivially() {
    let physics = module_with(Some(&[entity_region()]), None);
    let errs = verify_region_imports_from_module(&physics).unwrap();
    assert_eq!(errs, vec![]);
    let report = verify_link_graph(&[("physics", physics.as_slice())]).unwrap();
    assert_eq!(report.certificates, vec![]);
    assert_eq!(report.errors, vec![]);
}
