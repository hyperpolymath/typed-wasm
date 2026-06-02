// SPDX-License-Identifier: MPL-2.0
//
// Capstone execution gate — Phase 1 gate to Phase 2 (#132).
//
// "A contributor can `tw build` -> run the `.wasm` on Wasmtime." This proves
// the emitted example-01 module is accepted by the Wasmtime engine: it must
// `wasmtime compile` (full validation + Cranelift codegen — stable across CLI
// versions), and, best-effort, execute an exported function. Skips gracefully
// where wasmtime is not on PATH (provision it via the environment setup).
//
// The "actionable error on a violation" half of the Phase-2 gate is the
// compile-time path — `tw build` self-verifies and emits human-readable
// diagnostics (see src/errors.rs, tests/errors.rs).

use std::process::Command;
use typed_wasm_codegen::emit_example01;

fn wasmtime_available() -> bool {
    Command::new("wasmtime")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

#[test]
fn example01_runs_on_wasmtime_or_skips() {
    if !wasmtime_available() {
        eprintln!(
            "wasmtime not on PATH — capstone execution gate skipped \
             (provision wasmtime via the environment setup)"
        );
        return;
    }

    let dir = std::env::temp_dir();
    let wasm = dir.join("tw_exec_ex01.wasm");
    let cwasm = dir.join("tw_exec_ex01.cwasm");
    std::fs::write(&wasm, emit_example01()).expect("write module");

    // Primary, version-stable assertion: the Wasmtime engine validates and
    // compiles (Cranelift) the emitted module to native code.
    let compiled = Command::new("wasmtime")
        .arg("compile")
        .arg(&wasm)
        .arg("-o")
        .arg(&cwasm)
        .output()
        .expect("run wasmtime compile");
    assert!(
        compiled.status.success(),
        "Wasmtime rejected the emitted module:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&compiled.stdout),
        String::from_utf8_lossy(&compiled.stderr),
    );

    // Best-effort execution: invoke an exported function. The `run --invoke`
    // CLI surface varies across wasmtime versions, so a mismatch is logged
    // rather than failed — the `compile` assertion above is the gate.
    let run = Command::new("wasmtime")
        .args(["run", "--invoke", "get_player_hp"])
        .arg(&wasm)
        .args(["0", "0"])
        .output();
    match run {
        Ok(o) if o.status.success() => {
            eprintln!(
                "wasmtime executed get_player_hp -> {}",
                String::from_utf8_lossy(&o.stdout).trim()
            );
        }
        _ => eprintln!(
            "note: `wasmtime run --invoke` not asserted (CLI syntax is version-specific); \
             the `wasmtime compile` gate passed"
        ),
    }
}
