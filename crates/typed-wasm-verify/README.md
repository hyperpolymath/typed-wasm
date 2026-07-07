<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# typed-wasm-verify

Post-codegen verifier for typed-wasm **L7 (aliasing safety)** and **L10 (linearity)** constraints on emitted wasm modules.

## What it does

Given a wasm module that carries an `typedwasm.ownership` custom section, this crate:

1. **Intra-function check** — walks every function body and computes per-path `(min_uses, max_uses)` for each parameter. Linear params must be `(1, 1)` on every path; ExclBorrow params must have `max_uses ≤ 1`.
2. **Cross-module check** — given a callee's exported ownership interface plus a caller module that imports those functions, verifies that Linear-param imports are invoked exactly once per execution path.

The custom-section binary format:

```
u32le  count
for each entry:
  u32le  func_idx
  u8     n_params
  u8[n]  param_kinds  (0=Unrestricted, 1=Linear, 2=SharedBorrow, 3=ExclBorrow)
  u8     ret_kind
```

## Spec of record

**This crate + the Idris2 `VerifierSpec.idr` ARE the spec of record** (ADR-0008, 2026-07-07). The crate began as a Rust port of `hyperpolymath/affinescript`'s `lib/tw_verify.ml` / `lib/tw_interface.ml`; the parity criterion those files were pinned behind (workspace task C5) was met by `tests/cross_compat.rs` (synthetic table) + `tests/cross_compat_real.rs` (real producer bytes), and the crate has since grown past the OCaml reference (L13 both forms, L2/L15 carriers, link-graph certification, third-producer conformance). The OCaml files are a conforming implementation; on divergence, they are presumed wrong unless `src/abi/TypedWasm/ABI/VerifierSpec.idr` says otherwise.

## Consumers

- `hyperpolymath/ephapax` — calls into this crate as a Cargo dependency to verify its compile-eph output.
- `hyperpolymath/affinescript` — invokes the built binary as a subprocess, eventually replacing its OCaml verifier.
- **Third producer (Zig)** — `ffi/zig/src/twasm_producer.zig` hand-assembles wasm + the ownership carrier with no shared code; its committed fixtures (`tests/fixtures/zig_producer/`) are the producer-neutrality proof (`tests/third_producer_zig.rs`).

## Status

- [x] C1 — Scaffold (types, error enums, public entry stubs)
- [x] C2 — Custom-section parser (`src/section.rs`)
- [x] C3 — Per-path use-range analysis (L7+L10 intra-function, `src/verify.rs`; includes L13 negative-form module isolation)
- [x] C4 — Cross-module boundary verifier (`src/cross.rs`)
- [x] C5 — Cross-compat test against affinescript-emitted wasm (`tests/cross_compat.rs` synthetic parity table + `tests/cross_compat_real.rs` real fixtures under `tests/fixtures/c5_real/`)

Still open: L13 positive-form region-imports agreement (typed-wasm#140, proposal 0003) and carrier-backed L2–L6/L15 passes graduating from the `unstable-l2`/`unstable-l15` features.
