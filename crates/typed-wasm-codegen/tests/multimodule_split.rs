// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Per-module split (#140 remainder): `module Name { … }` blocks parse
// into separate Modules (`parse_modules`), importers are seeded with
// the producer's ACTUAL schema (real offsets + instance counts), each
// module emits its own wasm, and the link graph certifies agreement
// over genuinely separate binaries — the examples/02 killer feature as
// three real modules instead of one merged parse.

use typed_wasm_codegen::{emit, parser};
use typed_wasm_verify::{verify_link_graph, RegionImportsError, WasmTy};

const GAME: &str = include_str!("fixtures/multimodule/game.twasm");

#[test]
fn module_blocks_split_and_seed_importers() {
    let modules = parser::parse_modules(GAME).expect("game.twasm parses");
    let names: Vec<&str> = modules.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["physics", "ai", "render"]);

    let physics = &modules[0].1;
    assert_eq!(physics.regions[0].name, "Entity");
    assert_eq!(physics.region_imports.len(), 0);

    // The importer's Entity is the producer's ACTUAL schema (5 fields,
    // real byte size), not its 3-field expected subset — so accesses
    // lower against real offsets.
    let ai = &modules[1].1;
    assert_eq!(ai.region_imports.len(), 1);
    assert_eq!(ai.region_imports[0].expected_fields.len(), 3);
    assert_eq!(ai.regions[0].name, "Entity");
    assert_eq!(
        ai.regions[0].fields.len(),
        physics.regions[0].fields.len(),
        "seeded with the producer's actual schema"
    );
    assert_eq!(ai.regions[0].byte_size, physics.regions[0].byte_size);

    // Every module's functions lower for real.
    for (name, module) in &modules {
        for f in &module.funcs {
            assert!(
                !f.accesses.is_empty(),
                "{name}.{} must lower for real",
                f.name
            );
        }
    }
}

#[test]
fn split_modules_link_with_certificates() {
    let modules = parser::parse_modules(GAME).expect("game.twasm parses");
    let built: Vec<(String, Vec<u8>)> = modules
        .iter()
        .map(|(n, m)| (n.clone(), emit(m)))
        .collect();
    for (name, bytes) in &built {
        wasmparser::Validator::new()
            .validate_all(bytes)
            .unwrap_or_else(|e| panic!("{name} must validate: {e}"));
    }
    let graph: Vec<(&str, &[u8])> = built
        .iter()
        .map(|(n, b)| (n.as_str(), b.as_slice()))
        .collect();
    let report = verify_link_graph(&graph).expect("link graph runs");
    assert_eq!(report.errors, vec![], "clean graph");
    assert_eq!(report.certificates.len(), 2, "ai + render both certified");
}

#[test]
fn split_mutant_expectation_is_rejected_at_link() {
    let mut modules = parser::parse_modules(GAME).expect("game.twasm parses");
    let ai = &mut modules[1].1;
    ai.region_imports[0]
        .expected_fields
        .iter_mut()
        .find(|f| f.name == "flags")
        .unwrap()
        .wasm_ty = WasmTy::F64; // actual is u32
    let built: Vec<(String, Vec<u8>)> = modules
        .iter()
        .map(|(n, m)| (n.clone(), emit(m)))
        .collect();
    let graph: Vec<(&str, &[u8])> = built
        .iter()
        .map(|(n, b)| (n.as_str(), b.as_slice()))
        .collect();
    let report = verify_link_graph(&graph).expect("link graph runs");
    assert!(report
        .errors
        .iter()
        .any(|e| matches!(e, RegionImportsError::SchemaImportMismatch { .. })));
}

/// The merged single-module view (the corpus contract) still works on
/// module-block sources: blocks flatten, imports union-merge.
#[test]
fn merged_view_still_parses_module_blocks() {
    let merged = parser::parse_module(GAME).expect("merged parse");
    assert_eq!(merged.regions.len(), 1);
    assert_eq!(merged.funcs.len(), 3);
    assert_eq!(merged.region_imports.len(), 1, "imports union-merged");
}
