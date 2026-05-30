// SPDX-License-Identifier: MPL-2.0
//
// Round-trip soundness for codegen v0 (Phase 1, issue #124).
//
// The closed loop this crate exists to demonstrate:
//
//     emit(example01())  ->  valid wasm  ->  typed-wasm-verify accepts it
//
// This is the in-process form of the Phase 1 deliverable-2 property
// `verify(codegen(parse(src))) == OK` (issue #130), restricted to the
// single example codegen v0 covers. It also discharges Phase 0 gate 2
// (#48): "codegen v0 emits valid wasm for examples/01-single-module.twasm,
// verifiable end-to-end by typed-wasm-verify".

use typed_wasm_verify::{
    parse_regions_section_payload, verify_access_sites_from_module, verify_from_module,
    ACCESS_SITES_SECTION_NAME, REGIONS_SECTION_NAME,
};

#[test]
fn example01_is_well_formed_wasm() {
    let bytes = typed_wasm_codegen::emit_example01();
    // Full validation, not just lenient parsing: proves "emits valid wasm".
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .expect("emitted module must be valid wasm");
}

#[test]
fn example01_passes_l7_l10_verifier() {
    let bytes = typed_wasm_codegen::emit_example01();
    // No ownership section emitted (example 01 has no linear resources),
    // so the L7/L10 pass verifies trivially clean.
    verify_from_module(&bytes).expect("L7/L10 ownership pass must accept codegen v0 output");
}

#[test]
fn example01_passes_l2_access_site_verifier() {
    let bytes = typed_wasm_codegen::emit_example01();
    // The carrier-backed L2 pass: every access-site (region_id, field_id,
    // func_idx) must resolve against the emitted typedwasm.regions table.
    let violations =
        verify_access_sites_from_module(&bytes).expect("access-sites section must parse");
    assert!(
        violations.is_empty(),
        "codegen v0 emitted access-sites the verifier rejected: {violations:?}"
    );
}

#[test]
fn example01_embeds_both_l2_carriers() {
    let bytes = typed_wasm_codegen::emit_example01();
    let mut saw_regions = false;
    let mut saw_access = false;
    let mut regions_payload: Vec<u8> = Vec::new();

    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::CustomSection(c) = payload.expect("parse") {
            match c.name() {
                REGIONS_SECTION_NAME => {
                    saw_regions = true;
                    regions_payload = c.data().to_vec();
                }
                ACCESS_SITES_SECTION_NAME => saw_access = true,
                _ => {}
            }
        }
    }

    assert!(saw_regions, "expected a {REGIONS_SECTION_NAME} custom section");
    assert!(saw_access, "expected a {ACCESS_SITES_SECTION_NAME} custom section");

    // The regions carrier must decode to the three example-01 regions.
    let regions =
        parse_regions_section_payload(&regions_payload).expect("regions carrier must decode");
    let names: Vec<&str> = regions.iter().map(|r| r.name.as_str()).collect();
    assert_eq!(names, ["Vec2", "Players", "Enemies"]);
}
