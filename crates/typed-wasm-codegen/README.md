<!-- SPDX-License-Identifier: MPL-2.0 -->
# typed-wasm-codegen

The first in-tree `.twasm → .wasm` **producer** (codegen **v0**).

Before this crate the toolchain stopped at `source → Lexer → Parser →
Checker → diagnostics`; the only wasm-aware code was the *verifier*
(`typed-wasm-verify`). This crate closes Phase 0's gate 2 (issue #48) and
seeds Phase 1 (issue #49, deliverable 1).

## What it does

Lowers a typed region IR ([`Module`](src/lib.rs)) to:

- a **well-formed wasm module** with **real typed loads/stores at
  layout-computed offsets** (element `base + index*stride`, nested `.pos.x`
  into inline embedded regions), and
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

Beyond example 01 it wires **example 03** (ownership/linearity, L7–L10) —
`own`/`&mut`/`&` parameters via the `typedwasm.ownership` carrier, checked by
`verify_from_module` (`tests/example03.rs`) — and emits a wasm **`name`
section** so debuggers show real function names (`tests/names.rs`).

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
| Front-end (`.twasm`) → IR | **deferred** — v0 builds the IR for `example01` directly (seam tracked by #127) |
| `typedwasm.regions` + `typedwasm.access-sites` | **emitted**, verifier-accepted |
| WAT (text) emission | **emitted** via `--emit wat\|both` (#125) |
| `typedwasm.ownership` (L7/L10) | **emitted** — Linear/ExclBorrow/SharedBorrow (example 03 + multi-module callee), checked by `verify_from_module` |
| Multi-module (linear boundary) | **emitted** — callee export + caller import round-trip through `verify_cross_module` (#128) |
| Debug symbols (`name` section) | **emitted** — function names for debuggers (#129, first increment) |
| Function-body lowering | **real** — layout engine (offsets/stride/align, inline embedded regions) + typed loads/stores via a base-local (harvested from Zig `twasmc` #136); `if`/`region.scan` control flow still simplified |

## Example coverage (#127)

| Example | Levels | Status |
|---|---|---|
| `01-single-module` | L1–L6 (regions, typed access) | ✅ emitted + verified (`tests/roundtrip.rs`) |
| `03-ownership-linearity` | L7–L10 (`own`/`&mut`/`&`) | ✅ emitted + verified (`tests/example03.rs`) |
| multi-module (linear boundary) | L10 cross-module | ✅ emitted + verified (`tests/multimodule.rs`) |
| `02-multi-module` | L13 region-imports (positive) | ⛔ proposal 0003 `[draft]`, no verifier pass → #140 |
| `04-ecs-game` | L2–L6 | ⬜ not yet wired |
| `05-tropical-cost` | L11 (tropical) | ⛔ L11 draft; no verifier pass |
| `06-epistemic-sync` | L12 (epistemic) | ⛔ L12 draft; no verifier pass |

Full coverage (all 10 levels × all 6 examples + the front-end → IR seam) is #127.

## Where this goes next

- **#127** — remaining example coverage (`04`) + the front-end → IR JSON seam (the matrix above tracks per-example status).
- **#129** — full offset → source-line map (DWARF or wasm sourcemap); needs source spans from the #127 seam + accurate instruction-offset tracking. The `name` section landed here is the first increment.
- **#130** — ✅ landed: `verify(emit(m)) == OK` property corpus over 512 generated modules (`tests/corpus.rs`); the `parse(src)`-fed form awaits the #127 seam.
- **#140** — L13 positive-form / region-imports (`examples/02`); proposal 0003 `[draft]`.
