<!-- SPDX-License-Identifier: MPL-2.0 -->
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

## Usage

```sh
# build the example to wasm
cargo run -p typed-wasm-codegen --bin tw -- build examples/01-single-module.twasm -o /tmp/ex01.wasm

# the round-trip soundness test (emit → validate → verify)
cargo test -p typed-wasm-codegen
```

## Scope of v0 (see `docs/decisions/0004-codegen-host-language.adoc`)

| Aspect | v0 status |
|---|---|
| Host language / location | Rust crate, sibling of `typed-wasm-verify`, emits via `wasm-encoder` |
| Front-end (`.twasm`) → IR | **deferred** — v0 builds the IR for `example01` directly (seam tracked by #127) |
| `typedwasm.regions` + `typedwasm.access-sites` | **emitted**, verifier-accepted |
| `typedwasm.ownership` (L7/L10) | not emitted for example 01 (no linear resources); lands with `examples/03` under #127 |
| Function-body lowering | representative type-correct bodies, not full `region.scan`/indexing semantics |

## Where this goes next

- **#127** — codegen coverage across all 10 levels × all 6 examples (and the front-end → IR JSON seam).
- **#128** — multi-module codegen.
- **#130** — promote the round-trip test into the ECHIDNA property corpus.
- **#125** — WAT emission alongside the binary.
