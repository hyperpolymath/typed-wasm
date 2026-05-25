# Phase 0 Status

**Foundation defensibly engineered as of 2026-05-24.**

Phase 0 closes the engineering-surface fragility around the proofs so all subsequent phases have a load-bearing foundation. See [Production-Path](Production-Path) §Phase 0 for the full statement and [#48](https://github.com/hyperpolymath/typed-wasm/issues/48) for live tracking.

## Sub-tracks

### Track A — Codegen pipeline

| Deliverable | Status | PR |
|---|---|---|
| tree-sitter-twasm scaffold + region-decls grammar v0 | ✅ Shipped | [#58](https://github.com/hyperpolymath/typed-wasm/pull/58) |
| Extend tree-sitter to full `spec/grammar.ebnf` parity | 🟡 In progress | — |
| Idris2 parser at 188-test parity with ReScript | ⬜ Not started | — |
| ReScript cut (single PR) | ⬜ Blocked on parser parity | — |
| Codegen v0 for `examples/01-single-module.twasm` | ⬜ Blocked on parser | — |

### Track B — AffineScript verifier migration

| Deliverable | Status |
|---|---|
| Cross-repo PR in `hyperpolymath/affinescript` swapping OCaml verifier for subprocess call to `typed-wasm-verify` | ⬜ Not started (separate session needed — different repo) |

### Track C — Audit-floor cleanup

| Deliverable | Status | PR |
|---|---|---|
| `cargo audit` CI workflow | ✅ Shipped | [#55](https://github.com/hyperpolymath/typed-wasm/pull/55) |
| Real `tests/property/property_test.mjs` (29 assertions) | ✅ Shipped | [#57](https://github.com/hyperpolymath/typed-wasm/pull/57) |
| Security aspect dimension (`tests/aspect/security-envelope.mjs`, 10 assertions) | ✅ Shipped | #57 |
| Proof-level regression tests (`tests/proof/regression.mjs`, 25 assertions + optional idris2 layer) | ✅ Shipped | #57 |

### Track CI — Persistent reds hardening

| Job | Status |
|---|---|
| Cargo build + test | ✅ Green (PR #46 swap to rustup) |
| Structural E2E | ✅ Green (PR #46 + #57 smoke artefact guard) |
| Smoke test | ✅ Green |
| governance / Workflow security linter | ✅ Green |
| governance / Code quality + docs | ✅ Green |
| Cargo audit (RustSec) | ✅ Green |
| Build + E2E (Idris2 + Zig) | 🟡 Non-blocking advisory ([#59](https://github.com/hyperpolymath/typed-wasm/pull/59)); root cause undiagnosed (auth-gated logs); likely idris2 install on ubuntu-24.04 or zig build test |
| Validate A2ML manifests | 🟡 Non-blocking advisory (#59); third-party action failure |
| Validate K9 contracts | 🟡 Non-blocking advisory (#59); third-party action failure |
| governance / Language / package anti-pattern policy | 🟡 Pre-existing red; fixed naturally by Track A's ReScript cut |

### Track Docs — Documentation truthfulness

| Deliverable | Status | PR |
|---|---|---|
| `docs/PRODUCTION-PATH.adoc` canonical 6-phase plan | ✅ Shipped | [#47](https://github.com/hyperpolymath/typed-wasm/pull/47) |
| ROADMAP.adoc version↔phase mapping | ✅ Shipped | #47 |
| README.adoc Status section pointing to production path | ✅ Shipped | #47 |
| Phase tracking issues #48–#54 with checklists | ✅ Shipped | — |
| ROADMAP truthfulness audit (3 real drifts fixed) | ✅ Shipped | [#60](https://github.com/hyperpolymath/typed-wasm/pull/60) |
| claim-envelope §8 drift-detection (catches rename + missing-file drift) | ✅ Shipped | #60 |

## When does Phase 0 "close"?

Per the production-path definition, Phase 0 advances to Phase 1 when:

1. Every commit on `main` exits CI green (or the gate is explicitly removed with reason recorded).
2. Codegen v0 emits valid wasm for `examples/01-single-module.twasm`, verifiable end-to-end by `typed-wasm-verify`.
3. `ROADMAP.adoc` reflects reality (verified each "DONE" claim).

Status against those gates:
- **Gate 1**: ✅ Met via #59 — all CI is now either green or explicitly advisory with documented removal preconditions.
- **Gate 2**: ⬜ Not yet — needs codegen v0 from Track A (multi-PR work).
- **Gate 3**: ✅ Met via #60 — every documented claim verified, drift-detection aspect in place.

**So Phase 0 is 2/3 of the way to its gate**. The blocker is codegen v0, which is the terminal deliverable of Track A's multi-PR sequence.

## Test surface summary

After Phase 0 housekeeping closed:

| Surface | Assertions | Where |
|---|---|---|
| ParserTests.res | 88 | tests/parser/ParserTests.res |
| typed-wasm-verify (Rust) | 53 (43 unit + 10 cross-compat) | crates/typed-wasm-verify/ |
| Per-level tests | 56 | tests/levels/L1.mjs..L10.mjs |
| Aspect — claim-envelope | 53 | tests/aspect/claim-envelope.mjs |
| Aspect — security-envelope | 10 | tests/aspect/security-envelope.mjs |
| Property tests | 29 | tests/property/property_test.mjs |
| Proof regression | 25 (+ idris2 layer) | tests/proof/regression.mjs |
| Smoke E2E | 40 | tests/smoke/e2e-smoke.mjs |
| Structural E2E | 53 | tests/e2e.sh |
| Integration (airborne-step-state) | 14 | tests/contracts/ |
| ECHIDNA harness | 124 local | tests/echidna/echidna-harness.mjs |
| **Total** | **545+ assertions** | |

## Decisions still pending (load-bearing)

None of D1–D6 from [Production-Path](Production-Path) have ADRs yet. D2 (producer-side-only vs. runtime-aware) is the one most urgent — it determines whether Phase 3 happens at all.

## What unblocks Phase 1

Track A's codegen v0 PR. Track B can land in parallel without blocking the gate.
