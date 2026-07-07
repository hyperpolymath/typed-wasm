// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Producer-side coverage for examples/02-multi-module.twasm — the L13
// positive-form region-imports carrier (proposal 0003 / ADR-0007,
// issue #140). The example file holds three conceptual modules; the
// parser merges it into one module whose Entity region is local AND
// imported (module B and C both declare `import region Entity from
// "physics"` with different subsets — union-merged into one entry).

use typed_wasm_codegen::{emit, parser};
use typed_wasm_verify::{
    verify_link_graph, verify_region_imports_from_module, RegionImportsError, WasmTy,
};

const SRC: &str = include_str!("../../../examples/02-multi-module.twasm");

/// The parser records the two `import region Entity from "physics"`
/// declarations as ONE union-merged import-table entry (unique
/// (producer, region) pairs — proposal 0003 producer obligation).
#[test]
fn example02_parser_records_union_merged_import() {
    let module = parser::parse_module(SRC).expect("02-multi-module.twasm must parse");

    assert_eq!(module.region_imports.len(), 1, "one (physics, Entity) pair");
    let imp = &module.region_imports[0];
    assert_eq!(imp.producer_module, "physics");
    assert_eq!(imp.region_name, "Entity");

    // Union of module B's {pos_x,pos_y,pos_z,vel_x,vel_y,vel_z,flags}
    // and module C's {pos_x,pos_y,pos_z,scale,flags} = 8 fields.
    let names: Vec<&str> = imp.expected_fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(
        names,
        ["pos_x", "pos_y", "pos_z", "vel_x", "vel_y", "vel_z", "flags", "scale"],
        "union keeps first-seen order, appends new fields"
    );
    let flags = imp.expected_fields.iter().find(|f| f.name == "flags").unwrap();
    assert_eq!(flags.wasm_ty, WasmTy::U32);
}

/// Emitted example-02 carries the region-imports carrier, is internally
/// consistent, and — since the file also DEFINES Entity (module A) — a
/// self-link graph naming this module "physics" certifies agreement.
#[test]
fn example02_emits_carrier_and_self_link_agrees() {
    let module = parser::parse_module(SRC).expect("02-multi-module.twasm must parse");
    let wasm = emit(&module);

    let errs = verify_region_imports_from_module(&wasm).expect("wasm parses");
    assert_eq!(errs, vec![], "module-local import table must be consistent");

    let report = verify_link_graph(&[("physics", wasm.as_slice())]).expect("wasm parses");
    assert_eq!(report.errors, vec![], "expected subset must agree with actual Entity");
    assert_eq!(report.certificates.len(), 1);
    assert_eq!(report.certificates[0].producer, "physics");
    assert_eq!(report.certificates[0].region_name, "Entity");
}

/// Teeth: an importer whose expectation disagrees with the actual
/// export must be rejected at link time.
#[test]
fn example02_mutated_expectation_is_rejected() {
    let mut module = parser::parse_module(SRC).expect("02-multi-module.twasm must parse");
    module.region_imports[0]
        .expected_fields
        .iter_mut()
        .find(|f| f.name == "flags")
        .unwrap()
        .wasm_ty = WasmTy::F64; // actual Entity.flags is u32
    let wasm = emit(&module);

    let report = verify_link_graph(&[("physics", wasm.as_slice())]).expect("wasm parses");
    assert!(report.certificates.is_empty());
    assert!(matches!(
        &report.errors[..],
        [RegionImportsError::SchemaImportMismatch { type_mismatches, .. }]
            if type_mismatches.len() == 1 && type_mismatches[0].starts_with("flags")
    ));
}

/// A consumer alone in the graph (producer absent) must not certify.
#[test]
fn example02_without_producer_is_unresolved() {
    let module = parser::parse_module(SRC).expect("02-multi-module.twasm must parse");
    let wasm = emit(&module);
    // Register the module under a name nothing imports from.
    let report = verify_link_graph(&[("ai", wasm.as_slice())]).expect("wasm parses");
    assert!(matches!(
        &report.errors[..],
        [RegionImportsError::UnresolvedProducerModule { producer_module, .. }]
            if producer_module == "physics"
    ));
}
