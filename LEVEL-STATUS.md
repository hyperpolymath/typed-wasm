# SPDX-License-Identifier: PMPL-1.0-or-later
# typed-wasm Level Achievement Status

## Versioning Scheme

typed-wasm versions track the highest fully-achieved level tier:

| Version | Levels | Meaning |
|---------|--------|---------|
| v1.0 | L1-10 | Proven erasable stack (proofs + runtime L1-6, compile-time L7-10) |
| v1.1 | L11-12 | Tropical + epistemic (formalised → integrated into toolchain) |
| v2.0 | L13+ | Future levels (probabilistic, differential privacy, etc.) |

## Current: v1.0 (L1-10 complete, L11-12 formalised)

| Level | Name | Idris2 Proof | Zig FFI | Tests | Status |
|-------|------|-------------|---------|-------|--------|
| 1 | Instruction validity | Region.idr | Parser | ECHIDNA 10^5 | **E2E complete** |
| 2 | Region-binding | Region.idr + TypedAccess.idr | Schema lookup | ECHIDNA 10^5 | **E2E complete** |
| 3 | Type-compatible access | TypedAccess.idr | Typed load/store | ECHIDNA 10^5 | **E2E complete** |
| 4 | Null safety | Pointer.idr | Pointer kinds | ECHIDNA 10^5 | **E2E complete** |
| 5 | Bounds-proof | TypedAccess.idr + Levels.idr | Bounds check | ECHIDNA 10^5 | **E2E complete** |
| 6 | Result-type | TypedAccess.idr | Type flow | ECHIDNA 10^5 | **E2E complete** |
| 7 | Aliasing safety | Pointer.idr (Unique) | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased** |
| 8 | Effect-tracking | Effects.idr | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased** |
| 9 | Lifetime safety | Lifetime.idr | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased** |
| 10 | Linearity | Linear.idr (QTT q=1) | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased** |
| 11 | Tropical cost-tracking | Tropical.idr (0 believe_me) | Not yet | None | **Formalised [sfap]** |
| 12 | Epistemic safety | Epistemic.idr (0 believe_me) | Not yet | None | **Formalised [sfap]** |

**[sfap]** = "so far as possible" — proofs are machine-checked in Idris2 with
zero dangerous patterns. They are as complete as the Idris2 type checker can
verify. Full mechanical verification against a formal Wasm operational
semantics (e.g. WasmCert-Isabelle) remains future work.

## What "proven, erased" means

Levels 7-10 are verified by the Idris2 type checker at compile time, then
erased before code generation via QTT (Quantitative Type Theory). The
emitted Wasm is identical to hand-written code — zero runtime overhead.
This is by design, not a gap. The proofs exist to catch bugs at compile
time; they are not needed at runtime.

## What "formalised" means

Levels 11-12 have Idris2 type definitions and proof structures with zero
believe_me, but no Zig FFI implementation and no integration tests. They
are machine-checked mathematical definitions, not runnable code. Wiring
them into the toolchain is the v1.1 milestone.

## Proof inventory (0 believe_me across all files)

| File | Lines | believe_me | postulate | assert_total |
|------|-------|-----------|-----------|-------------|
| Region.idr | - | 0 | 0 | 0 |
| TypedAccess.idr | - | 0 | 0 | 0 |
| Levels.idr | - | 0 | 0 | 0 |
| Pointer.idr | - | 0 | 0 | 0 |
| Effects.idr | - | 0 | 0 | 0 |
| Lifetime.idr | - | 0 | 0 | 0 |
| Linear.idr | - | 0 | 0 | 0 |
| MultiModule.idr | - | 0 | 0 | 0 |
| Proofs.idr | - | 0 | 0 | 0 |
| Tropical.idr | - | 0 | 0 | 0 |
| Epistemic.idr | - | 0 | 0 | 0 |
