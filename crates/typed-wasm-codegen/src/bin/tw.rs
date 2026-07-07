// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! `tw` — the typed-wasm build CLI (codegen v0).
//!
//! Usage:
//!   tw build <file.twasm> [-o <out>] [--emit wasm|wat|both] [--split]
//!   tw link <a.wasm> <b.wasm> …
//!
//! `--split` emits one wasm per top-level `module Name { … }` block
//! (`<out>.<module>.wasm`); `link` runs the L13 cross-module link-graph
//! pass (ADR-0007) over already-built modules, naming each by its file
//! stem, and reports certificates / violations.

use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("build") => build(&args[2..]),
        Some("link") => link(&args[2..]),
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
    eprintln!("usage: tw build <file.twasm> [-o <out>] [--emit wasm|wat|both] [--split]");
    eprintln!("       tw link <a.wasm> <b.wasm> ...");
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
    let mut split = false;
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
            "--split" => split = true,
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

    if split {
        return build_split(&input, &src, output.as_deref(), emit);
    }

    // Parse via the canonical Rust front-end (ADR-0006).
    let bytes = match typed_wasm_codegen::parser::parse_module(&src) {
        Ok(module) => {
            let bytes = typed_wasm_codegen::emit(&module);
            // Try to self-verify the emitted module
            if let Err(diagnostics) = typed_wasm_codegen::self_verify(&module) {
                for msg in diagnostics {
                    eprintln!("tw build: self-verify warning: {}", msg);
                }
            }
            bytes
        }
        Err(e) => {
            // A parse failure is authoritative: report the diagnostic and exit
            // non-zero. Previously this silently fell back to hardcoded-schema
            // string-matching, which masked real parse errors with a confusing
            // double message. The Rust parser now covers the example +
            // paint-type schemas and general `.twasm`, so the fallback is gone.
            eprintln!("tw build: parse error in '{input}': {e}");
            return ExitCode::FAILURE;
        }
    };
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

/// `tw build --split`: one output per `module Name { … }` block.
fn build_split(input: &str, src: &str, output: Option<&str>, emit: Emit) -> ExitCode {
    let modules = match typed_wasm_codegen::parser::parse_modules(src) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("tw build: parse error in '{input}': {e}");
            return ExitCode::FAILURE;
        }
    };
    let base = output.unwrap_or(input);
    let stem = Path::new(base)
        .with_extension("")
        .to_string_lossy()
        .into_owned();
    let mut wrote = Vec::new();
    for (name, module) in &modules {
        let bytes = typed_wasm_codegen::emit(module);
        if let Err(diagnostics) = typed_wasm_codegen::self_verify(module) {
            for msg in diagnostics {
                eprintln!("tw build: self-verify warning [{name}]: {msg}");
            }
        }
        if emit.wants_wasm() {
            let path = format!("{stem}.{name}.wasm");
            if let Err(e) = std::fs::write(&path, &bytes) {
                eprintln!("tw build: cannot write '{path}': {e}");
                return ExitCode::FAILURE;
            }
            wrote.push(format!("{path} ({} bytes)", bytes.len()));
        }
        if emit.wants_wat() {
            let path = format!("{stem}.{name}.wat");
            let text = typed_wasm_codegen::wat(&bytes);
            if let Err(e) = std::fs::write(&path, text.as_bytes()) {
                eprintln!("tw build: cannot write '{path}': {e}");
                return ExitCode::FAILURE;
            }
            wrote.push(path);
        }
    }
    eprintln!(
        "tw build: split {} module(s): {}",
        modules.len(),
        wrote.join(" + ")
    );
    eprintln!("tw build: check cross-module schema agreement with `tw link <files…>`.");
    ExitCode::SUCCESS
}

/// `tw link`: the L13 positive-form link-graph pass (ADR-0007) over
/// built modules. Each module's wasm-level name is its file stem's last
/// dot-segment (`game.physics.wasm` → `physics`).
fn link(files: &[String]) -> ExitCode {
    if files.is_empty() {
        eprintln!("tw link: no modules given");
        usage();
        return ExitCode::FAILURE;
    }
    let mut named: Vec<(String, Vec<u8>)> = Vec::new();
    for f in files {
        let bytes = match std::fs::read(f) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("tw link: cannot read '{f}': {e}");
                return ExitCode::FAILURE;
            }
        };
        let stem = Path::new(f)
            .with_extension("")
            .file_name()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| f.clone());
        let name = stem.rsplit('.').next().unwrap_or(&stem).to_string();
        named.push((name, bytes));
    }
    let graph: Vec<(&str, &[u8])> = named
        .iter()
        .map(|(n, b)| (n.as_str(), b.as_slice()))
        .collect();
    match typed_wasm_verify::verify_link_graph(&graph) {
        Ok(report) => {
            for c in &report.certificates {
                println!(
                    "CERTIFIED  {} imports {}.{}",
                    c.consumer, c.producer, c.region_name
                );
            }
            for e in &report.errors {
                eprintln!("VIOLATION  {e}");
            }
            if report.errors.is_empty() {
                eprintln!(
                    "tw link: {} module(s), {} certificate(s), no violations",
                    named.len(),
                    report.certificates.len()
                );
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(e) => {
            eprintln!("tw link: wasm parse error: {e}");
            ExitCode::FAILURE
        }
    }
}

/// `base` with its extension replaced by `ext`
/// (e.g. `with_extension("foo.twasm", "wasm")` -> `"foo.wasm"`).
fn with_extension(base: &str, ext: &str) -> String {
    Path::new(base)
        .with_extension(ext)
        .to_string_lossy()
        .into_owned()
}
