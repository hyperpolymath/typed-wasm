<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# zig_producer fixtures — the third `typedwasm.ownership` producer

Wasm modules hand-assembled byte-by-byte by
`ffi/zig/src/twasm_producer.zig` — a producer sharing **no ancestry**
with AffineScript (OCaml), Ephapax (Rust), or the in-tree Rust codegen.
Their acceptance/rejection by `typed-wasm-verify`
(`tests/third_producer_zig.rs`) demonstrates the carrier contract is
producer-neutral: any toolchain in any language that writes the
documented bytes participates in L7/L10 verification.

| File | Body of `consume(x: Linear i32)` | Expected verdict |
|---|---|---|
| `zig_clean_linear.wasm` | `local.get 0; drop` (once) | **accepted** |
| `zig_double_use.wasm` | `local.get 0; drop` twice | **rejected** (`UsedMoreThanOnce` — a wasm-level double-free) |

Captured 2026-07-07 with Zig 0.15.2. Regenerate after changing the
generator with:

```bash
cd ffi/zig && zig build gen-fixtures
```

The generator is deterministic (asserted by its own `zig build test`
suite), so a regeneration with an unchanged generator is byte-identical.
