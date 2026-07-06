// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Codegen coverage for examples/03-ownership-linearity.twasm — L7–L10
// (Phase 1 deliverable 1 / #127).
//
// The full source→parse→emit→verify pipeline over the L7–L10 flagship
// example: the parser must translate the source's `own` / `&mut` / `&`
// qualifiers into `Module::ownership` entries, the emitted wasm must carry
// the `typedwasm.ownership` section with exactly those kinds on the wire,
// and the verifier must both accept the honest module and reject a
// double-consume mutant (so the pass has teeth, not vacuous green).

use typed_wasm_codegen::{emit, parser, Op, Ownership};
use typed_wasm_verify::{
    parse_ownership_section_payload, verify_from_module, OwnershipKind, VerifyError,
    OWNERSHIP_SECTION_NAME,
};
use wasmparser::{Parser as WasmParser, Payload};

const SRC: &str = include_str!("../../../examples/03-ownership-linearity.twasm");

/// Extract the `typedwasm.ownership` custom-section payload from wasm bytes.
fn ownership_payload(wasm: &[u8]) -> Option<Vec<u8>> {
    for payload in WasmParser::new(0).parse_all(wasm) {
        if let Ok(Payload::CustomSection(reader)) = payload {
            if reader.name() == OWNERSHIP_SECTION_NAME {
                return Some(reader.data().to_vec());
            }
        }
    }
    None
}

/// The parser records the source's ownership qualifiers into the IR:
/// every function that asks for L7–L10 discipline gets an entry, and
/// all-Unrestricted functions stay out of the carrier.
#[test]
fn example03_parser_records_ownership_signatures() {
    let module = parser::parse_module(SRC).expect("03-ownership-linearity.twasm must parse");

    let by_name = |name: &str| {
        let idx = module
            .funcs
            .iter()
            .position(|f| f.name == name)
            .unwrap_or_else(|| panic!("function {name} must be parsed"));
        module.ownership.iter().find(|(i, _, _)| *i == idx)
    };

    // spawn_particle: six scalar params, returns `own region<Particle>`.
    let (_, params, ret) = by_name("spawn_particle").expect("spawn_particle carries discipline");
    assert!(params.iter().all(|k| *k == Ownership::Unrestricted));
    assert_eq!(*ret, Ownership::Linear, "own return is Linear");

    // despawn_particle(particle: own region<Particle>) — Linear param.
    let (_, params, ret) = by_name("despawn_particle").expect("despawn_particle has discipline");
    assert_eq!(params[0], Ownership::Linear);
    assert_eq!(*ret, Ownership::Unrestricted);

    // update_particle(p: &mut region<Particle>, dt: f32) — ExclBorrow.
    let (_, params, _) = by_name("update_particle").expect("update_particle has discipline");
    assert_eq!(params[0], Ownership::ExclBorrow);
    assert_eq!(params[1], Ownership::Unrestricted);

    // read_particle_pos(p: &region<Particle>) — SharedBorrow.
    let (_, params, _) = by_name("read_particle_pos").expect("read_particle_pos has discipline");
    assert_eq!(params[0], Ownership::SharedBorrow);

    // find_nearest_alive / safe_batch_update: borrow + scalars.
    let (_, params, _) = by_name("find_nearest_alive").expect("find_nearest_alive has discipline");
    assert_eq!(params[0], Ownership::SharedBorrow);
    let (_, params, _) = by_name("safe_batch_update").expect("safe_batch_update has discipline");
    assert_eq!(params[0], Ownership::ExclBorrow);

    // particle_lifecycle() takes no params and returns nothing — no entry.
    assert!(
        by_name("particle_lifecycle").is_none(),
        "all-Unrestricted signature must stay out of the carrier"
    );
}

/// The emitted wasm carries the ownership kinds on the wire, byte-decodable
/// by the verifier's own section parser, and the module verifies.
#[test]
fn example03_emits_ownership_carrier_and_verifies() {
    let module = parser::parse_module(SRC).expect("03-ownership-linearity.twasm must parse");
    let wasm = emit(&module);

    let payload =
        ownership_payload(&wasm).expect("emitted example03 must carry typedwasm.ownership");
    let entries = parse_ownership_section_payload(&payload);
    assert_eq!(
        entries.len(),
        module.ownership.len(),
        "one wire entry per disciplined function"
    );

    // Wire spot-checks (example03 has no imports, so global idx == local idx).
    let despawn_idx = module
        .funcs
        .iter()
        .position(|f| f.name == "despawn_particle")
        .unwrap() as u32;
    let despawn = entries
        .iter()
        .find(|e| e.func_idx == despawn_idx)
        .expect("despawn_particle on the wire");
    assert_eq!(despawn.param_kinds[0], OwnershipKind::Linear);

    let spawn_idx = module
        .funcs
        .iter()
        .position(|f| f.name == "spawn_particle")
        .unwrap() as u32;
    let spawn = entries
        .iter()
        .find(|e| e.func_idx == spawn_idx)
        .expect("spawn_particle on the wire");
    assert_eq!(spawn.ret_kind, OwnershipKind::Linear, "own return on the wire");

    verify_from_module(&wasm).expect("honest example03 must pass L7/L10");
}

/// Teeth: consuming despawn_particle's Linear param twice (a double-free at
/// the wasm level) must be rejected by the verifier — proving the carrier
/// emitted from parsed source is load-bearing, not decorative.
#[test]
fn example03_double_free_mutant_is_rejected() {
    let mut module = parser::parse_module(SRC).expect("03-ownership-linearity.twasm must parse");
    let despawn_idx = module
        .funcs
        .iter()
        .position(|f| f.name == "despawn_particle")
        .expect("despawn_particle must be parsed");
    module.funcs[despawn_idx].body =
        vec![Op::LocalGet(0), Op::Drop, Op::LocalGet(0), Op::Drop];
    module.funcs[despawn_idx].accesses.clear();

    let wasm = emit(&module);
    match verify_from_module(&wasm) {
        Err(VerifyError::Ownership(errs)) => {
            assert!(
                !errs.is_empty(),
                "double-free must surface at least one ownership error"
            );
        }
        Err(other) => panic!("expected an ownership rejection, got: {other:?}"),
        Ok(()) => panic!("double-free mutant must NOT verify"),
    }
}
