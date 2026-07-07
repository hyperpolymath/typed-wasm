// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Third-producer conformance: `typedwasm.ownership` emitted by a Zig
// program (`ffi/zig/src/twasm_producer.zig`) that hand-assembles wasm
// bytes and shares no code with AffineScript, Ephapax, or the in-tree
// Rust codegen. The verifier accepting the honest module and rejecting
// the double-consume mutant proves the carrier contract is
// producer-neutral — the independence property of an actual compile
// TARGET, not a companion library. Fixture provenance:
// tests/fixtures/zig_producer/README.md.

use typed_wasm_verify::{
    extract_exports, verify_from_module, OwnershipError, OwnershipKind, VerifyError,
};

const CLEAN: &[u8] = include_bytes!("fixtures/zig_producer/zig_clean_linear.wasm");
const DOUBLE_USE: &[u8] = include_bytes!("fixtures/zig_producer/zig_double_use.wasm");

/// The Zig-emitted module is structurally valid wasm.
#[test]
fn zig_fixtures_are_valid_wasm() {
    for (name, bytes) in [("clean", CLEAN), ("double_use", DOUBLE_USE)] {
        wasmparser::Validator::new()
            .validate_all(bytes)
            .unwrap_or_else(|e| panic!("{name} fixture must be valid wasm: {e}"));
    }
}

/// The honest module — Linear param consumed exactly once — verifies.
#[test]
fn zig_clean_linear_is_accepted() {
    verify_from_module(CLEAN).expect("Zig-emitted clean module must pass L7/L10");
}

/// The verifier reads the Zig-written carrier exactly as a first-party
/// one: one exported function, one Linear param, Unrestricted return.
#[test]
fn zig_ownership_interface_extracts_correctly() {
    let exports = extract_exports(CLEAN).expect("interface extraction");
    assert_eq!(exports.len(), 1);
    let f = &exports[0];
    assert_eq!(f.name, "consume");
    assert_eq!(f.param_kinds, vec![OwnershipKind::Linear]);
    assert_eq!(f.ret_kind, OwnershipKind::Unrestricted);
}

/// The double-consume mutant — a wasm-level double-free — is rejected.
#[test]
fn zig_double_use_is_rejected() {
    match verify_from_module(DOUBLE_USE) {
        Err(VerifyError::Ownership(errs)) => {
            assert!(
                errs.iter().any(|e| matches!(
                    e,
                    OwnershipError::LinearUsedMultiple { func_idx: 0, param_idx: 0, .. }
                )),
                "expected a Linear multi-use rejection, got: {errs:?}"
            );
        }
        other => panic!("double-use mutant must be rejected with an ownership error: {other:?}"),
    }
}
