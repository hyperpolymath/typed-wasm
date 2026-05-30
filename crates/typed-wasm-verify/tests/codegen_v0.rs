// SPDX-License-Identifier: MPL-2.0
//
// Codegen v0 end-to-end gate (PRODUCTION-PATH.adoc Phase 0 gate 2).
//
// `src/codegen/` (the Zig `twasmc` producer) compiles
// `examples/01-single-module.twasm` to the wasm module checked in at
// `tests/fixtures/codegen_v0/01-single-module.wasm`. This suite is the
// blocking, Rust-only proof that the producer's output is
//
//   1. structurally valid wasm, and
//   2. accepted by `typed-wasm-verify` end-to-end.
//
// The fixture is producer-emitted bytes (same pattern as
// `tests/fixtures/c5_real/`); see that directory's README for the
// regenerate procedure. The Zig toolchain is not required to run this
// test — only to regenerate the fixture.

use std::path::Path;

use typed_wasm_verify::{
    parse_ownership_section_payload, verify_from_module, OwnershipKind, OWNERSHIP_SECTION_NAME,
};
use wasmparser::{Parser, Payload};

fn golden() -> Vec<u8> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/codegen_v0/01-single-module.wasm");
    std::fs::read(&p).unwrap_or_else(|e| panic!("cannot read codegen-v0 fixture {p:?}: {e}"))
}

fn custom_section(bytes: &[u8], name: &str) -> Option<Vec<u8>> {
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CustomSection(reader) = payload.expect("parse") {
            if reader.name() == name {
                return Some(reader.data().to_vec());
            }
        }
    }
    None
}

// ----------------------------------------------------------------------
// Core gate (default features) — runs in CI `cargo test --workspace`
// ----------------------------------------------------------------------

#[test]
fn codegen_v0_example01_is_structurally_valid_wasm() {
    let bytes = golden();
    let mut v = wasmparser::Validator::new();
    v.validate_all(&bytes)
        .expect("codegen v0 output must be structurally valid wasm");
}

#[test]
fn codegen_v0_example01_passes_ownership_verifier() {
    let bytes = golden();
    let verdict = verify_from_module(&bytes);
    assert!(
        verdict.is_ok(),
        "codegen v0 output must pass L7/L10/L13 ownership verification, got {verdict:?}"
    );
}

#[test]
fn codegen_v0_example01_ownership_carrier_matches_handle_modes() {
    let bytes = golden();
    let payload =
        custom_section(&bytes, OWNERSHIP_SECTION_NAME).expect("typedwasm.ownership section present");
    let entries = parse_ownership_section_payload(&payload);
    assert_eq!(entries.len(), 5, "example 01 declares five functions");

    let kind = |idx: u32| entries.iter().find(|e| e.func_idx == idx).unwrap().param_kinds[0];
    // `&mut region<Players>` => ExclBorrow (damage_player, move_player).
    assert_eq!(kind(1), OwnershipKind::ExclBorrow, "damage_player param 0");
    assert_eq!(kind(4), OwnershipKind::ExclBorrow, "move_player param 0");
    // `&region<Players>` => SharedBorrow (get_player_hp).
    assert_eq!(kind(0), OwnershipKind::SharedBorrow, "get_player_hp param 0");
}

// ----------------------------------------------------------------------
// L2 carrier gate (feature `unstable-l2`)
// ----------------------------------------------------------------------

#[cfg(feature = "unstable-l2")]
#[test]
fn codegen_v0_example01_access_sites_verify_clean() {
    let bytes = golden();
    let errs =
        typed_wasm_verify::verify_access_sites_from_module(&bytes).expect("access-site pass runs");
    assert!(errs.is_empty(), "access-site violations: {errs:?}");
}

#[cfg(feature = "unstable-l2")]
#[test]
fn codegen_v0_example01_carriers_are_substantive() {
    let bytes = golden();

    let regions_pl = custom_section(&bytes, typed_wasm_verify::REGIONS_SECTION_NAME)
        .expect("typedwasm.regions section present");
    let regions =
        typed_wasm_verify::parse_regions_section_payload(&regions_pl).expect("regions parse");
    assert_eq!(regions.len(), 3, "Vec2 + Players + Enemies");

    let access_pl = custom_section(&bytes, typed_wasm_verify::ACCESS_SITES_SECTION_NAME)
        .expect("typedwasm.access-sites section present");
    let sites = typed_wasm_verify::section::parse_access_sites_section_payload(&access_pl)
        .expect("access-sites parse");
    // get_player_hp(1) + damage_player(3) + get_enemy_target_hp(2)
    //   + count_active_enemies(1) + move_player(4) = 11 typed accesses.
    assert_eq!(sites.len(), 11, "one entry per typed access in example 01");
}
