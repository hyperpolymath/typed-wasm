// SPDX-License-Identifier: MPL-2.0
//
// C5.1 — real-AffineScript-emitted .wasm fixtures (typed-wasm#35 part 2).
//
// Companion to `tests/cross_compat.rs`. That suite synthesises wasm
// modules with `wasm_encoder` and hand-traces the expected verdicts;
// this suite loads bytes that `affinescript compile` actually emitted
// and asserts the verifier reaches the same conclusion. The synthetic
// table is the parity oracle; this is the cross-check.
//
// Fixture sources, provenance, and the regenerate procedure live in
// `tests/fixtures/c5_real/README.adoc`.

use std::path::Path;

use typed_wasm_verify::{verify_from_module, OwnershipError, VerifyError};

fn fixture_path(name: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/c5_real")
        .join(name)
}

fn load(name: &str) -> Vec<u8> {
    std::fs::read(fixture_path(name))
        .unwrap_or_else(|e| panic!("cannot read fixture {name}: {e}"))
}

// ----------------------------------------------------------------------
// Clean fixtures — must verify Ok(())
// ----------------------------------------------------------------------

#[test]
fn c5_01_clean_linear_consumer_passes() {
    let bytes = load("01_clean_linear.wasm");
    let verdict = verify_from_module(&bytes);
    assert!(
        verdict.is_ok(),
        "expected Ok, got {verdict:?} \
         (fixture is `@linear` consumed exactly once via let-rebind; \
         affinescript codegen drift?)"
    );
}

#[test]
fn c5_02_shared_borrow_twice_passes() {
    let bytes = load("02_shared_borrow_twice.wasm");
    let verdict = verify_from_module(&bytes);
    assert!(
        verdict.is_ok(),
        "expected Ok, got {verdict:?} \
         (fixture reads `ref Int` twice in one expression — SharedBorrow \
         allows arbitrary reads; verifier should not flag)"
    );
}

// ----------------------------------------------------------------------
// Violation fixtures — must produce specific OwnershipError variants
// ----------------------------------------------------------------------

#[test]
fn c5_03_partial_drop_flags_dropped_on_some_path() {
    let bytes = load("03_partial_drop.wasm");
    let verdict = verify_from_module(&bytes);
    match verdict {
        Err(VerifyError::Ownership(errs)) => {
            assert!(
                errs.iter()
                    .any(|e| matches!(e, OwnershipError::LinearDroppedOnSomePath { .. })),
                "expected at least one LinearDroppedOnSomePath; got {errs:?}"
            );
            // The sink fn body discards its own-typed param entirely; the
            // verifier should also flag a LinearNotUsed for that function.
            assert!(
                errs.iter()
                    .any(|e| matches!(e, OwnershipError::LinearNotUsed { .. })),
                "expected LinearNotUsed for the sink fn; got {errs:?}"
            );
        }
        other => panic!("expected Err(Ownership(..)), got {other:?}"),
    }
}

#[test]
fn c5_04_excl_borrow_alias_flags_aliased() {
    let bytes = load("04_excl_alias.wasm");
    let verdict = verify_from_module(&bytes);
    match verdict {
        Err(VerifyError::Ownership(errs)) => {
            assert!(
                errs.iter().any(|e| matches!(
                    e,
                    OwnershipError::ExclBorrowAliased { count, .. } if *count >= 2
                )),
                "expected ExclBorrowAliased (count >= 2); got {errs:?}"
            );
        }
        other => panic!("expected Err(Ownership(..)), got {other:?}"),
    }
}

// ----------------------------------------------------------------------
// Sanity — every fixture file referenced above must exist (catches a
// rebase that drops a binary while leaving the test in place).
// ----------------------------------------------------------------------

#[test]
fn c5_fixture_inventory_intact() {
    for name in &[
        "01_clean_linear.affine",
        "01_clean_linear.wasm",
        "02_shared_borrow_twice.affine",
        "02_shared_borrow_twice.wasm",
        "03_partial_drop.affine",
        "03_partial_drop.wasm",
        "04_excl_alias.affine",
        "04_excl_alias.wasm",
        "README.adoc",
    ] {
        assert!(
            fixture_path(name).exists(),
            "missing fixture: tests/fixtures/c5_real/{name}"
        );
    }
}
