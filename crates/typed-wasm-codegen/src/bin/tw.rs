// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! `tw` — the typed-wasm build CLI (codegen v0).
//!
//! Usage:
//!   tw build <file.twasm> [-o <out.wasm>]
//!
//! v0 supports only the example-01 schema; general `.twasm` front-end →
//! IR lowering is tracked in ADR-0004 and issue #127.

use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("build") => build(&args[2..]),
        Some("--version") | Some("-V") => {
            println!("tw {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some("--help") | Some("-h") | None => {
            usage();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("tw: unknown subcommand '{other}'");
            usage();
            ExitCode::FAILURE
        }
    }
}

fn usage() {
    eprintln!("usage: tw build <file.twasm> [-o <out.wasm>]");
}

fn build(rest: &[String]) -> ExitCode {
    let mut input: Option<String> = None;
    let mut output: Option<String> = None;
    let mut i = 0;
    while i < rest.len() {
        match rest[i].as_str() {
            "-o" | "--output" => {
                i += 1;
                match rest.get(i) {
                    Some(o) => output = Some(o.clone()),
                    None => {
                        eprintln!("tw build: -o requires a path");
                        return ExitCode::FAILURE;
                    }
                }
            }
            s if !s.starts_with('-') => input = Some(s.to_string()),
            other => {
                eprintln!("tw build: unknown option '{other}'");
                return ExitCode::FAILURE;
            }
        }
        i += 1;
    }

    let Some(input) = input else {
        eprintln!("tw build: missing input .twasm file");
        usage();
        return ExitCode::FAILURE;
    };

    let src = match std::fs::read_to_string(&input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("tw build: cannot read '{input}': {e}");
            return ExitCode::FAILURE;
        }
    };

    // v0 gate: confirm the input is (structurally) the example-01 schema
    // before emitting its baked IR. The general front-end → IR seam is
    // deferred per ADR-0004 (tracked by #127).
    let is_example01 = src.contains("region Players")
        && src.contains("region Enemies")
        && src.contains("memory game_memory");
    if !is_example01 {
        eprintln!(
            "tw build: codegen v0 only supports the example-01 schema \
             (regions Players + Enemies and `memory game_memory`)."
        );
        eprintln!(
            "           General .twasm front-end -> IR lowering is tracked \
             in ADR-0004 and issue #127."
        );
        return ExitCode::FAILURE;
    }

    let bytes = typed_wasm_codegen::emit_example01();

    let out = output.unwrap_or_else(|| default_output(&input));
    if let Err(e) = std::fs::write(&out, &bytes) {
        eprintln!("tw build: cannot write '{out}': {e}");
        return ExitCode::FAILURE;
    }

    eprintln!(
        "tw build: wrote {out} ({} bytes) — carriers: typedwasm.regions + typedwasm.access-sites \
         (verify with `typed-wasm-verify`).",
        bytes.len()
    );
    ExitCode::SUCCESS
}

/// Default output path: input filename with its extension replaced by `.wasm`.
fn default_output(input: &str) -> String {
    let p = Path::new(input);
    p.with_extension("wasm").to_string_lossy().into_owned()
}
