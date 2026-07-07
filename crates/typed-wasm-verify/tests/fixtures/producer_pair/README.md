<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# producer_pair fixtures — producer-emitted cross-module ownership boundary

The producer-emitted callee/caller differential pair issue #140 asked
for: `typed-wasm-codegen`'s `multimodule_callee()` / `multimodule_caller(n)`
IR emitted to real bytes and committed, exercised by
`tests/producer_pair.rs` against `extract_exports` + `verify_cross_module`.

| File | Content | Expected verdict |
|---|---|---|
| `callee.wasm` | exports `consume(x: Linear)` with an ownership carrier | interface extracts: `[Linear] → Unrestricted` |
| `caller_ok.wasm` | imports `consume`, calls it exactly once | **accepted** |
| `caller_double.wasm` | imports `consume`, calls it twice | **rejected** (`LinearImportCalledMultiple`) |

Captured 2026-07-07. Regenerate after producer changes with the
one-shot generator (deterministic — an unchanged producer regenerates
byte-identical files):

```bash
cargo run -p typed-wasm-codegen --example gen_producer_pair  # (recreate from git history if pruned)
```

The in-crate parity oracle remains `typed-wasm-codegen/tests/multimodule.rs`;
this pair pins the emitted **bytes** so byte-level drift in either the
producer or the verifier shows up as a fixture diff, mirroring
`c5_real/` (AffineScript) and `zig_producer/` (Zig).
