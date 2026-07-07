// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Human-readable error messages — Phase 1 deliverable 6 (#126).
//
// The translation layer turns the verifier's index-keyed rejections into
// actionable, function-name-anchored messages, and the producer self-checks
// its own output so a codegen bug surfaces as a message a contributor can
// act on (the Phase-2 gate's "error message they can act on").

use typed_wasm_codegen::{
    example01, humanize, self_verify, Func, Module, Op, Ownership, Wty,
};
use typed_wasm_verify::{OwnershipError, VerifyError};

#[test]
fn clean_examples_self_verify() {
    assert!(
        self_verify(&example01()).is_ok(),
        "example 01 should self-verify clean"
    );
    // example03 source→emit→verify coverage lives in tests/example03.rs
}

#[test]
fn double_free_gives_named_actionable_message() {
    // An `own` handle used twice — the message must name the function, cite
    // the level, and state the rule.
    let module = Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "despawn_particle".into(),
            params: vec![Wty::I32],
            results: vec![],
            locals: vec![],
            body: vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop],
            accesses: vec![],
            export: true,
        }],
        ownership: vec![(0, vec![Ownership::Linear], Ownership::Unrestricted)],
        region_imports: vec![],
    };
    let diagnostics = self_verify(&module).expect_err("double-free must be rejected");
    let joined = diagnostics.join("\n");
    assert!(
        joined.contains("despawn_particle"),
        "message must name the function: {joined}"
    );
    assert!(
        joined.contains("L10"),
        "message must cite the level: {joined}"
    );
    assert!(
        joined.contains("exactly once"),
        "message must explain the rule: {joined}"
    );
}

#[test]
fn humanize_resolves_function_index_to_name() {
    // Use example01 which has well-known function names
    let module = example01();
    let err = VerifyError::Ownership(vec![OwnershipError::LinearUsedMultiple {
        func_idx: 0,
        param_idx: 0,
        count: 2,
    }]);
    let msgs = humanize(&module, &err);
    assert_eq!(msgs.len(), 1);
    assert!(
        msgs[0].contains("get_player_hp"),
        "index 0 should resolve to the function name: {}",
        msgs[0]
    );
}
