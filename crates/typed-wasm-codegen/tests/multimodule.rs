// SPDX-License-Identifier: MPL-2.0
//
// Multi-module codegen at verifier parity — Phase 1 deliverable 7 (#128).
//
// Producer-side emission for the verifier's *existing* cross-module
// coverage: the L10 linear-ownership import boundary. The callee exports a
// Linear-consuming function (with a typedwasm.ownership carrier); a caller
// imports it. `verify_cross_module` accepts a single call per path and
// rejects duplication.
//
// The L13 positive-form shared-region schema agreement that
// examples/02-multi-module.twasm shows (export/import region) rides the
// typedwasm.region-imports carrier (proposal 0003 [draft], no verifier
// pass yet) and is intentionally out of scope here.

use typed_wasm_codegen::{emit, emit_multimodule, multimodule_callee, multimodule_caller};
use typed_wasm_verify::{
    extract_exports, verify_cross_module, verify_from_module, CrossError, OwnershipKind,
    VerifyError,
};

#[test]
fn callee_and_caller_are_valid_wasm() {
    let (callee, caller) = emit_multimodule();
    wasmparser::Validator::new()
        .validate_all(&callee)
        .expect("callee must be valid wasm");
    wasmparser::Validator::new()
        .validate_all(&caller)
        .expect("caller must be valid wasm");
}

#[test]
fn callee_exposes_linear_consume_via_extract_exports() {
    let callee = emit(&multimodule_callee());
    let iface = extract_exports(&callee).expect("interface extracts");
    assert_eq!(iface.len(), 1);
    assert_eq!(iface[0].name, "consume");
    assert_eq!(iface[0].param_kinds, vec![OwnershipKind::Linear]);
}

#[test]
fn callee_is_intra_function_clean() {
    // The callee consumes its own Linear param exactly once.
    let callee = emit(&multimodule_callee());
    verify_from_module(&callee).expect("callee L7/L10 must be clean");
}

#[test]
fn clean_single_call_passes_cross_module() {
    let callee = emit(&multimodule_callee());
    let caller = emit(&multimodule_caller(1));
    let iface = extract_exports(&callee).unwrap();
    verify_cross_module(&iface, &caller).expect("one linear call across the boundary is clean");
}

#[test]
fn double_call_is_rejected_cross_module() {
    let callee = emit(&multimodule_callee());
    let caller = emit(&multimodule_caller(2));
    let iface = extract_exports(&callee).unwrap();
    match verify_cross_module(&iface, &caller) {
        Err(VerifyError::Cross(errs)) => {
            assert!(
                errs.iter()
                    .any(|e| matches!(e, CrossError::LinearImportCalledMultiple { count: 2, .. })),
                "expected LinearImportCalledMultiple, got {errs:?}"
            );
        }
        other => panic!("expected a cross-module rejection, got {other:?}"),
    }
}
