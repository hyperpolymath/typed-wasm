// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Producer-emitted cross-module differential pair (#140): the in-tree
// producer's callee/caller bytes are committed and pinned here against
// the L10 linear import boundary — `extract_exports` on the callee,
// `verify_cross_module` on the callers. Provenance:
// tests/fixtures/producer_pair/README.md.

use typed_wasm_verify::{
    extract_exports, verify_cross_module, CrossError, OwnershipKind, VerifyError,
};

const CALLEE: &[u8] = include_bytes!("fixtures/producer_pair/callee.wasm");
const CALLER_OK: &[u8] = include_bytes!("fixtures/producer_pair/caller_ok.wasm");
const CALLER_DOUBLE: &[u8] = include_bytes!("fixtures/producer_pair/caller_double.wasm");

#[test]
fn producer_pair_fixtures_are_valid_wasm() {
    for (name, bytes) in [
        ("callee", CALLEE),
        ("caller_ok", CALLER_OK),
        ("caller_double", CALLER_DOUBLE),
    ] {
        wasmparser::Validator::new()
            .validate_all(bytes)
            .unwrap_or_else(|e| panic!("{name} must be valid wasm: {e}"));
    }
}

#[test]
fn callee_interface_extracts_linear_consume() {
    let exports = extract_exports(CALLEE).expect("callee interface");
    let consume = exports
        .iter()
        .find(|f| f.name == "consume")
        .expect("callee exports consume");
    assert_eq!(consume.param_kinds, vec![OwnershipKind::Linear]);
}

#[test]
fn caller_calling_once_is_accepted() {
    let exports = extract_exports(CALLEE).expect("callee interface");
    verify_cross_module(&exports, CALLER_OK)
        .expect("single call of a Linear import is clean");
}

#[test]
fn caller_calling_twice_is_rejected() {
    let exports = extract_exports(CALLEE).expect("callee interface");
    match verify_cross_module(&exports, CALLER_DOUBLE) {
        Err(VerifyError::Cross(errs)) => assert!(
            errs.iter()
                .any(|e| matches!(e, CrossError::LinearImportCalledMultiple { .. })),
            "expected LinearImportCalledMultiple, got: {errs:?}"
        ),
        other => panic!("double call must be rejected with a Cross error: {other:?}"),
    }
}
