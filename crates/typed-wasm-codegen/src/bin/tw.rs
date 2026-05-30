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
    eprintln!("usage: tw build <file.twasm> [-o <out>] [--emit wasm|wat|both]");
}

/// What `tw build` emits.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Emit {
    Wasm,
    Wat,
    Both,
}

impl Emit {
    fn parse(s: &str) -> Option<Emit> {
        match s {
            "wasm" => Some(Emit::Wasm),
            "wat" => Some(Emit::Wat),
            "both" => Some(Emit::Both),
            _ => None,
        }
    }
    fn wants_wasm(self) -> bool {
        matches!(self, Emit::Wasm | Emit::Both)
    }
    fn wants_wat(self) -> bool {
        matches!(self, Emit::Wat | Emit::Both)
    }
}

fn build(rest: &[String]) -> ExitCode {
    let mut input: Option<String> = None;
    let mut output: Option<String> = None;
    let mut emit = Emit::Wasm;
    let mut i = 0;
    while i < rest.len() {
        let arg = rest[i].as_str();
        match arg {
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
            "--emit" => {
                i += 1;
                match rest.get(i).map(String::as_str).and_then(Emit::parse) {
                    Some(e) => emit = e,
                    None => {
                        eprintln!("tw build: --emit requires a value (wasm|wat|both)");
                        return ExitCode::FAILURE;
                    }
                }
            }
            a if a.starts_with("--emit=") => match Emit::parse(&a["--emit=".len()..]) {
                Some(e) => emit = e,
                None => {
                    eprintln!("tw build: --emit must be one of wasm|wat|both");
                    return ExitCode::FAILURE;
                }
            },
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
    // before emitting its baked IR. The general front-end -> IR seam is
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

    // v0 emits only the example-01 module; render the bytes once, then
    // write the requested artifact(s).
    let bytes = typed_wasm_codegen::emit_example01();
    let base = output.unwrap_or_else(|| input.clone());
    let mut wrote: Vec<String> = Vec::new();

    if emit.wants_wasm() {
        let path = with_extension(&base, "wasm");
        if let Err(e) = std::fs::write(&path, &bytes) {
            eprintln!("tw build: cannot write '{path}': {e}");
            return ExitCode::FAILURE;
        }
        wrote.push(format!("{path} ({} bytes)", bytes.len()));
    }
    if emit.wants_wat() {
        let text = typed_wasm_codegen::wat(&bytes);
        let path = with_extension(&base, "wat");
        if let Err(e) = std::fs::write(&path, text.as_bytes()) {
            eprintln!("tw build: cannot write '{path}': {e}");
            return ExitCode::FAILURE;
        }
        wrote.push(format!("{path} ({} bytes)", text.len()));
    }

    eprintln!(
        "tw build: wrote {} — carriers: typedwasm.regions + typedwasm.access-sites \
         (verify with `typed-wasm-verify`).",
        wrote.join(" + ")
    );
    ExitCode::SUCCESS
}

/// `base` with its extension replaced by `ext`
/// (e.g. `with_extension("foo.twasm", "wasm")` -> `"foo.wasm"`).
fn with_extension(base: &str, ext: &str) -> String {
    Path::new(base).with_extension(ext).to_string_lossy().into_owned()
}
