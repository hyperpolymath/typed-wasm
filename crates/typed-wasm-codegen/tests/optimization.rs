// SPDX-License-Identifier: MPL-2.0
//
// Optimization invariant-preservation — Phase 1 deliverable 3 (#131).
//
// The optimization story (docs/optimization.adoc) is: optimize with external
// wasm-opt (Binaryen), use typed-wasm-verify as the invariant oracle. These
// tests pin the two preservation HAZARDS the doc's vetted pass list guards
// against (verifiable in-repo without wasm-opt), plus a graceful-skip gate
// that runs a real wasm-opt round-trip where the tool is available.

use std::process::Command;
use typed_wasm_codegen::{emit, emit_example01, Body, Func, Module, Op, Ownership, Wty};
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_from_module, OwnershipError, VerifyError,
    ACCESS_SITES_SECTION_NAME, OWNERSHIP_SECTION_NAME, REGIONS_SECTION_NAME,
};

fn custom_section_names(bytes: &[u8]) -> Vec<String> {
    let mut names = Vec::new();
    for p in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CustomSection(c) = p.expect("parse") {
            names.push(c.name().to_string());
        }
    }
    names
}

/// HAZARD 1 — stripping custom sections makes verification vacuous.
/// example 01 carries the sections the verifier checks; a carrier-free module
/// is "accepted" only because there is nothing to check. An optimizer that
/// drops custom sections silently turns the former into the latter.
#[test]
fn stripping_carriers_makes_verification_vacuous() {
    let names = custom_section_names(&emit_example01());
    assert!(names.iter().any(|n| n == REGIONS_SECTION_NAME));
    assert!(names.iter().any(|n| n == ACCESS_SITES_SECTION_NAME));
    assert!(names.iter().any(|n| n == OWNERSHIP_SECTION_NAME));

    let bare = emit(&Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "f".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: Body::Ops(vec![Op::LocalGet(0), Op::Drop]),
            export: true,
        }],
        ownership: vec![],
    });
    assert!(
        custom_section_names(&bare)
            .iter()
            .all(|n| !n.starts_with("typedwasm.")),
        "the bare module must carry no typedwasm.* sections"
    );
    // No carriers ⇒ accepted vacuously (the stripping hazard).
    verify_from_module(&bare).expect("carrier-free module verifies vacuously");
    assert!(verify_access_sites_from_module(&bare).unwrap().is_empty());
}

/// HAZARD 2 — the ownership carrier's `func_idx` is load-bearing: identical
/// code, a different `func_idx` in the carrier, a different verdict. Any pass
/// that reorders/removes/merges functions invalidates it.
#[test]
fn ownership_func_idx_is_load_bearing() {
    // Two functions of identical shape, each using its param twice.
    let funcs = || {
        let dup = || Body::Ops(vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop]);
        vec![
            Func {
                name: "a".into(),
                params: vec![Wty::I32],
                results: vec![],
                body: dup(),
                export: true,
            },
            Func {
                name: "b".into(),
                params: vec![Wty::I32],
                results: vec![],
                body: dup(),
                export: true,
            },
        ]
    };
    let mk = |owned: usize| Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: funcs(),
        ownership: vec![(owned, vec![Ownership::Linear])],
    };

    // Carrier marks func 0 Linear → its double-use is the violation.
    match verify_from_module(&emit(&mk(0))) {
        Err(VerifyError::Ownership(es)) => assert!(es
            .iter()
            .any(|e| matches!(e, OwnershipError::LinearUsedMultiple { func_idx: 0, .. }))),
        o => panic!("expected a violation on func 0, got {o:?}"),
    }
    // Same code, carrier moved to func 1 → the violation now lands on func 1.
    match verify_from_module(&emit(&mk(1))) {
        Err(VerifyError::Ownership(es)) => assert!(es
            .iter()
            .any(|e| matches!(e, OwnershipError::LinearUsedMultiple { func_idx: 1, .. }))),
        o => panic!("expected a violation on func 1, got {o:?}"),
    }
}

/// The end-to-end gate: optimize with wasm-opt, then the verifier must still
/// accept. Skips gracefully where wasm-opt is unavailable (the vetted pass
/// list + flags are in docs/optimization.adoc).
#[test]
fn wasm_opt_gate_or_skip() {
    if Command::new("wasm-opt").arg("--version").output().is_err() {
        eprintln!("wasm-opt not on PATH — optimization gate skipped (see docs/optimization.adoc)");
        return;
    }
    let dir = std::env::temp_dir();
    let inp = dir.join("tw_opt_in.wasm");
    let outp = dir.join("tw_opt_out.wasm");
    std::fs::write(&inp, emit_example01()).expect("write input");

    // Function-identity-preserving passes only (see docs/optimization.adoc).
    let status = Command::new("wasm-opt")
        .args(["--vacuum", "--optimize-instructions", "--simplify-locals"])
        .arg("-o")
        .arg(&outp)
        .arg(&inp)
        .status()
        .expect("run wasm-opt");
    assert!(status.success(), "wasm-opt invocation failed");

    let opt = std::fs::read(&outp).expect("read optimized");
    wasmparser::Validator::new()
        .validate_all(&opt)
        .expect("optimized module is valid wasm");
    verify_from_module(&opt).expect("optimized module still passes L7/L10");
}
