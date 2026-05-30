// SPDX-License-Identifier: MPL-2.0
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
// This is the executable that makes "verifiable end-to-end by
// `typed-wasm-verify`" (PRODUCTION-PATH.adoc Phase 0 gate 2) a single
// command rather than a library call. The codegen-v0 producer in
// `src/codegen/` emits modules this binary accepts.

use std::process::ExitCode;

use typed_wasm_verify::verify_from_module;

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
        Err(e) => {
            eprintln!("tw-verify: ownership verification FAILED: {e}");
            return ExitCode::FAILURE;
        }
    }

    // 3. L2 per-instruction access-site verification (unstable carrier).
    #[cfg(feature = "unstable-l2")]
    match typed_wasm_verify::verify_access_sites_from_module(&bytes) {
        Ok(errs) if errs.is_empty() => println!("ok  L2 access-site verification"),
        Ok(errs) => {
            eprintln!("tw-verify: access-site violations: {errs:?}");
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
            eprintln!("tw-verify: capability violations: {errs:?}");
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
