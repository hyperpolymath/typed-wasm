// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// `tw-verify` — command-line front-end for the typed-wasm verifier.
//
// Reads a `.wasm` module from a path argument and runs, in order:
//   1. structural wasm validation (wasmparser `Validator`)
//   2. L7/L10/L13 ownership verification (`verify_from_module`)
//   3. L2 access-site verification (feature `unstable-l2`)
//   4. L15 capability verification (feature `unstable-l15`)
//
// Exit codes: 0 = verified, 1 = a check failed, 2 = usage / I/O error.
//
// Diagnostic format (#126): violations are printed as a level-prefixed
// bulleted list grouped by function-index, so a regression points at a
// named function rather than a `[…]` debug-dump. Source-line resolution
// ("at .twasm line N") defers to #129 (source maps).

use std::process::ExitCode;

use typed_wasm_verify::{verify_from_module, OwnershipError, VerifyError};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 || args[1] == "-h" || args[1] == "--help" {
        eprintln!("usage: tw-verify <module.wasm>");
        eprintln!();
        eprintln!("Runs structural wasm validation followed by the typed-wasm");
        eprintln!("ownership (L7/L10/L13) and, when built with --features");
        eprintln!("unstable-l2 / unstable-l15, the access-site (L2) and");
        eprintln!("capability (L15) verifier passes.");
        return ExitCode::from(2);
    }
    let path = &args[1];

    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("tw-verify: cannot read {path}: {e}");
            return ExitCode::from(2);
        }
    };

    // 1. Structural validity — every typed-wasm module is first a valid
    //    wasm module. A producer that emits malformed bytes fails here.
    let mut validator = wasmparser::Validator::new();
    if let Err(e) = validator.validate_all(&bytes) {
        eprintln!("tw-verify: INVALID wasm: {e}");
        return ExitCode::FAILURE;
    }
    println!("ok  structural wasm validation ({} bytes)", bytes.len());

    // 2. L7 (aliasing) + L10 (linearity) + L13 (module isolation).
    match verify_from_module(&bytes) {
        Ok(()) => println!("ok  L7/L10/L13 ownership verification"),
        Err(VerifyError::Ownership(errs)) => {
            print_ownership_violations(&errs);
            return ExitCode::FAILURE;
        }
        Err(VerifyError::Cross(errs)) => {
            print_cross_violations(&errs);
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!("tw-verify: verification error: {e}");
            return ExitCode::FAILURE;
        }
    }

    // 3. L2 per-instruction access-site verification (unstable carrier).
    #[cfg(feature = "unstable-l2")]
    match typed_wasm_verify::verify_access_sites_from_module(&bytes) {
        Ok(errs) if errs.is_empty() => println!("ok  L2 access-site verification"),
        Ok(errs) => {
            eprintln!(
                "FAIL L2 access-site verification ({} violation(s)):",
                errs.len()
            );
            for e in &errs {
                eprintln!("  - {e}");
            }
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!("tw-verify: access-site verify error: {e}");
            return ExitCode::FAILURE;
        }
    }

    // 4. L15 capability-lattice verification (unstable carrier).
    #[cfg(feature = "unstable-l15")]
    match typed_wasm_verify::verify_capabilities_from_module(&bytes) {
        Ok(errs) if errs.is_empty() => println!("ok  L15 capability verification"),
        Ok(errs) => {
            eprintln!(
                "FAIL L15 capability verification ({} violation(s)):",
                errs.len()
            );
            for e in &errs {
                eprintln!("  - {e}");
            }
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!("tw-verify: capability verify error: {e}");
            return ExitCode::FAILURE;
        }
    }

    println!("VERIFIED {path}");
    ExitCode::SUCCESS
}

/// Group OwnershipErrors by their func_idx (or by "(module-scope)" for
/// the L13 `ModuleNotIsolated` variant which has no func_idx), and print
/// a bulleted list under each header. Within a function, errors are
/// sorted by param_idx then by Display.
fn print_ownership_violations(errs: &[OwnershipError]) {
    use std::collections::BTreeMap;

    let mut by_func: BTreeMap<String, Vec<&OwnershipError>> = BTreeMap::new();
    for e in errs {
        let key = match e {
            OwnershipError::LinearNotUsed { func_idx, .. }
            | OwnershipError::LinearDroppedOnSomePath { func_idx, .. }
            | OwnershipError::LinearUsedMultiple { func_idx, .. }
            | OwnershipError::ExclBorrowAliased { func_idx, .. } => format!("function #{func_idx}"),
            OwnershipError::ModuleNotIsolated { .. } => "(module-scope)".to_string(),
        };
        by_func.entry(key).or_default().push(e);
    }

    eprintln!(
        "FAIL L7/L10/L13 ownership verification ({} violation(s) in {} location(s)):",
        errs.len(),
        by_func.len()
    );
    for (loc, group) in &by_func {
        eprintln!("  in {loc}:");
        let mut sorted: Vec<&&OwnershipError> = group.iter().collect();
        sorted.sort_by_key(|e| match e {
            OwnershipError::LinearNotUsed { param_idx, .. }
            | OwnershipError::LinearDroppedOnSomePath { param_idx, .. }
            | OwnershipError::LinearUsedMultiple { param_idx, .. }
            | OwnershipError::ExclBorrowAliased { param_idx, .. } => *param_idx,
            OwnershipError::ModuleNotIsolated { .. } => 0,
        });
        for e in sorted {
            eprintln!("    - {e}");
        }
    }
}

/// Group CrossErrors by caller_func_idx. Print bulleted list per caller.
fn print_cross_violations(errs: &[typed_wasm_verify::CrossError]) {
    use std::collections::BTreeMap;
    use typed_wasm_verify::CrossError;

    let mut by_caller: BTreeMap<u32, Vec<&CrossError>> = BTreeMap::new();
    for e in errs {
        let caller = match e {
            CrossError::LinearImportCalledMultiple {
                caller_func_idx, ..
            }
            | CrossError::LinearImportDroppedOnSomePath {
                caller_func_idx, ..
            } => *caller_func_idx,
        };
        by_caller.entry(caller).or_default().push(e);
    }

    eprintln!(
        "FAIL L10 cross-module boundary verification ({} violation(s) in {} caller(s)):",
        errs.len(),
        by_caller.len()
    );
    for (caller, group) in &by_caller {
        eprintln!("  in caller function #{caller}:");
        for e in group {
            eprintln!("    - {e}");
        }
    }
}
