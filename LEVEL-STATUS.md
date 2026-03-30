# SPDX-License-Identifier: PMPL-1.0-or-later
# typed-wasm Level Achievement Status

## Versioning Scheme

typed-wasm versions track the highest fully-achieved level tier:

| Version | Levels | Meaning |
|---------|--------|---------|
| v0.1 | L1-10 | Checked proof core (proofs + runtime L1-6, compile-time L7-10) |
| v1.0 | L1-10 | Audited release of the checked core |
| v1.1 | L11-12 | Tropical + epistemic integrated only after they type-check, enter the package, and gain test coverage |
| v2.0 | L13+ | Future levels (probabilistic, differential privacy, etc.) |

## Current: checked core = L1-10, L11-L12 = draft only

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
| 11 | Tropical cost-tracking | Tropical.idr | Not yet | None | **Draft only; not in package; standalone check currently fails** |
| 12 | Epistemic safety | Epistemic.idr | Not yet | None | **Draft only; not in package; standalone check currently fails** |

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

## What "draft" means

Levels 11-12 currently have draft Idris2 files and example syntax, but they are
not part of `typed-wasm.ipkg` and, as of 2026-03-30, both standalone checks
fail. Zero dangerous patterns is not enough here: a file that does not
type-check is not a claimable proof artefact. Wiring these levels into the
toolchain remains future work.

## Proof inventory

| File | believe_me | postulate | assert_total | Checked status |
|------|-----------|-----------|--------------|----------------|
| Region.idr | 0 | 0 | 0 | In package |
| TypedAccess.idr | 0 | 0 | 0 | In package |
| Levels.idr | 0 | 0 | 0 | In package |
| Pointer.idr | 0 | 0 | 0 | In package |
| Effects.idr | 0 | 0 | 0 | In package |
| Lifetime.idr | 0 | 0 | 0 | In package |
| Linear.idr | 0 | 0 | 0 | In package |
| MultiModule.idr | 0 | 0 | 0 | In package |
| Proofs.idr | 0 | 0 | 0 | In package |
| Tropical.idr | 0 | 0 | 0 | Draft file; standalone check fails |
| Epistemic.idr | 0 | 0 | 0 | Draft file; standalone check fails |
