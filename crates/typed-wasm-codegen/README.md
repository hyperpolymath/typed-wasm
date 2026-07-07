<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# typed-wasm-codegen

The first in-tree `.twasm → .wasm` **producer** (codegen **v0**).

Before this crate the toolchain stopped at `source → Lexer → Parser →
Checker → diagnostics`; the only wasm-aware code was the *verifier*
(`typed-wasm-verify`). This crate closes Phase 0's gate 2 (issue #48) and
seeds Phase 1 (issue #49, deliverable 1).

## What it does

Lowers a typed region IR ([`Module`](src/lib.rs)) to:

- a **well-formed wasm module** (linear memory + type-correct function
  bodies), and
- the L2–L6 carrier sections **`typedwasm.regions`** (ADR-0002) and
  **`typedwasm.access-sites`** (ADR-0003),

using `typed-wasm-verify`'s *own* carrier encoders, so the emitted bytes
cannot drift from the decoder the verifier runs. The output round-trips
through `verify_from_module` + `verify_access_sites_from_module`
in-process — see `tests/roundtrip.rs`.

It also emits **multi-module** pairs — a Linear-exporting callee (with a
`typedwasm.ownership` carrier) and an importing caller — that round-trip
through `extract_exports` + `verify_cross_module` (#128); see
`tests/multimodule.rs`.

## Usage

```sh
# build the example to wasm
cargo run -p typed-wasm-codegen --bin tw -- build examples/01-single-module.twasm -o /tmp/ex01.wasm

# emit the WAT (text) debug view, or both binary + text
cargo run -p typed-wasm-codegen --bin tw -- build examples/01-single-module.twasm -o /tmp/ex01 --emit wat
cargo run -p typed-wasm-codegen --bin tw -- build examples/01-single-module.twasm -o /tmp/ex01 --emit both

# the round-trip + WAT tests (emit → validate → verify)
cargo test -p typed-wasm-codegen
```

## Scope of v0 (see `docs/decisions/0004-codegen-host-language.adoc`)

| Aspect | v0 status |
|---|---|
| Host language / location | Rust crate, sibling of `typed-wasm-verify`, emits via `wasm-encoder` |
| Front-end (`.twasm`) → IR | **in-process Rust parser** (`src/parser.rs`) — all six `examples/*.twasm` parse → emit → verify (`tests/corpus.rs`), incl. ownership qualifiers → `typedwasm.ownership` (ADR-0006) |
| `typedwasm.regions` + `typedwasm.access-sites` | **emitted**, verifier-accepted |
| WAT (text) emission | **emitted** via `--emit wat\|both` (#125) |
| `typedwasm.ownership` (L7/L10) | **emitted** for any `own`/`&mut`/`&` source discipline (parser-recorded, incl. Linear returns) and for the multi-module callee (#128) |
| Multi-module (linear boundary) | **emitted** — callee export + caller import round-trip through `verify_cross_module` (#128) |
| Function-body lowering | **real statement lowering** — `let`, assignment, `if`/`else`, `while`, indexed `region.get`/`region.set`, `cast<>` (wasmi-executed, `tests/example04.rs`); `region.scan` and `opt<T>` unwraps still stub |

## Where this goes next

- **#127** — codegen coverage across all 10 levels × all 6 examples (and the front-end → IR JSON seam).
- **#130** — promote the round-trip tests into the ECHIDNA property corpus.
- **L13 positive-form / region-imports** — **done** (issue #140): `import region … from "…" { … }` parses into `Module::region_imports`, emits the `typedwasm.region-imports` carrier (proposal 0003 `[accepted]` / ADR-0007), and `verify_link_graph` certifies cross-module schema agreement (`tests/example02.rs`).
