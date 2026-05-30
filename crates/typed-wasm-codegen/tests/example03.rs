// SPDX-License-Identifier: MPL-2.0
//
// Codegen coverage for examples/03-ownership-linearity.twasm — L7–L10
// (Phase 1 deliverable 1 / #127).
//
// The producer emits the typedwasm.ownership carrier (Linear / ExclBorrow /
// SharedBorrow) and bodies that satisfy the verifier's use-count discipline,
// so the module round-trips through verify_from_module. A deliberately
// broken double-free is rejected — the carrier has teeth.

use typed_wasm_codegen::{emit, emit_example03, AccessSite, Func, Module, Op, Ownership, Wty};
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_from_module, OwnershipError, VerifyError,
};

#[test]
fn example03_is_valid_wasm() {
    let bytes = emit_example03();
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .expect("example 03 must be valid wasm");
}

#[test]
fn example03_passes_l7_l10_ownership() {
    // despawn (Linear, used once), update (ExclBorrow, referenced once),
    // read (SharedBorrow, unconstrained), spawn (Unrestricted) — all clean.
    let bytes = emit_example03();
    verify_from_module(&bytes).expect("example 03 L7/L10 ownership must be clean");
}

#[test]
fn example03_passes_l2_access_sites() {
    let bytes = emit_example03();
    let violations =
        verify_access_sites_from_module(&bytes).expect("access-sites section must parse");
    assert!(
        violations.is_empty(),
        "example 03 emitted access-sites the verifier rejected: {violations:?}"
    );
}

#[test]
fn double_free_is_rejected() {
    // A Linear (own) handle used twice — a double-free the verifier must
    // catch (LinearUsedMultiple), proving the ownership carrier is enforced
    // on emitted bytes, not just declared.
    let module = Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "double_free".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop],
            accesses: Vec::<AccessSite>::new(),
            export: true,
        }],
        ownership: vec![(0, vec![Ownership::Linear])],
    };
    let bytes = emit(&module);
    match verify_from_module(&bytes) {
        Err(VerifyError::Ownership(errs)) => assert!(
            errs.iter()
                .any(|e| matches!(e, OwnershipError::LinearUsedMultiple { count: 2, .. })),
            "expected LinearUsedMultiple, got {errs:?}"
        ),
        other => panic!("expected an ownership rejection, got {other:?}"),
    }
}
