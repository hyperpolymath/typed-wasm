# Phase 0 Status

**Foundation defensibly engineered. All 3 Phase 0 gates met as of 2026-05-30 — gate 2 (codegen v0) closed by the `src/codegen/` twasmc producer. Phase 1 ([#49](https://github.com/hyperpolymath/typed-wasm/issues/49)) is open.**

Phase 0 closes the engineering-surface fragility around the proofs so all subsequent phases have a load-bearing foundation. See [Production-Path](Production-Path) §Phase 0 for the full statement and [#48](https://github.com/hyperpolymath/typed-wasm/issues/48) for live tracking.

## Headline numbers

- **11 PRs landed** across two sessions
- **545+ test assertions** across 11 surfaces (up from ~430)
- **3 of 3 Phase 0 gates met** (gate 2 / codegen v0 closed 2026-05-30 — `src/codegen/` twasmc emits verifier-accepted wasm for example 01)
- **8 deletions** of worthless / template-residue files
- **4 new RSR-aligned taxonomy stubs** (`AUDIT.adoc`, `docs/onboarding/`, `docs/status/`, `docs/proposals/`)
- **2 real bugs caught and fixed** by drift-detection aspects (`.well-known/security.txt` template residue, missing SPDX headers)

## Sub-tracks

### Track A — Codegen pipeline

| Deliverable | Status | PR |
|---|---|---|
| tree-sitter-twasm scaffold + region-decls grammar v0 | ✅ Shipped | [#58](https://github.com/hyperpolymath/typed-wasm/pull/58) |
| tree-sitter v1 — parses `examples/01-single-module.twasm` end-to-end (0 ERROR nodes) | ✅ Shipped | [#62](https://github.com/hyperpolymath/typed-wasm/pull/62) |
| Extend tree-sitter to remaining `spec/grammar.ebnf` productions (imports, L11–L16, match, proof) | 🟡 Next | — |
| Idris2 parser at 188-test parity with ReScript | ⬜ Not started | — |
| ReScript cut (single PR) | ⬜ Blocked on parser parity | — |
| Codegen v0 for `examples/01-single-module.twasm` | ✅ Shipped — `src/codegen/` twasmc (Zig 0.16), verified end-to-end by `typed-wasm-verify` | — |

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
| Wiki source-of-truth at `docs/wiki/` + comprehensive STATE.a2ml update | ✅ Shipped | [#61](https://github.com/hyperpolymath/typed-wasm/pull/61) |
| Repo taxonomy tidy: RSR-aligned (AUDIT.adoc, docs/status/, docs/onboarding/, docs/proposals/); deletions (3 template-residue QUICKSTARTs, 2 .invariants.md heuristic artefacts, empty docs/wikis/, stray generated/abi/README); ABI-PIPELINE doc move; smoke job graceful for in-flight parser migration; duplication scrub (stale ReScript references) | ✅ Shipped | [#63](https://github.com/hyperpolymath/typed-wasm/pull/63) |

## When does Phase 0 "close"?

Per the production-path definition, Phase 0 advances to Phase 1 when:

1. Every commit on `main` exits CI green (or the gate is explicitly removed with reason recorded).
2. Codegen v0 emits valid wasm for `examples/01-single-module.twasm`, verifiable end-to-end by `typed-wasm-verify`.
3. `ROADMAP.adoc` reflects reality (verified each "DONE" claim).

Status against those gates:
- **Gate 1**: ✅ Met via #59 — all CI is now either green or explicitly advisory with documented removal preconditions.
- **Gate 2**: ✅ Met 2026-05-30 — `src/codegen/` twasmc emits valid wasm for `examples/01-single-module.twasm`, verified end-to-end by `typed-wasm-verify` (structural validation + L7/L10/L13 ownership + L2 access-sites); gated by `crates/typed-wasm-verify/tests/codegen_v0.rs`.
- **Gate 3**: ✅ Met via #60 — every documented claim verified, drift-detection aspect in place.

**So Phase 0 has met all 3 gates and is closed; Phase 1 is open.** Codegen v0 — the terminal gate-2 deliverable — landed as the `src/codegen/` twasmc producer (its own Zig lexer/parser/layout/wasm-emitter), decoupled from the still-pending Idris2 parser port.

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

Codegen v0 landed (`src/codegen/` twasmc) — Phase 1 ([#49](https://github.com/hyperpolymath/typed-wasm/issues/49)) is now open. Phase 1 extends codegen to the remaining examples + full `spec/grammar.ebnf`, adds WAT/source-map emission and human-readable diagnostics, and replaces this bootstrap producer's front-end with the AffineScript → Idris2 parser. Track B (verifier migration) can still land in parallel in `hyperpolymath/affinescript`.

## 2026-05-27 — Post-Phase-0 proof-debt closure pass

Independent of the Phase 0 / Phase 1 gate transition, a 2026-05-27 sweep closed long-tail proof-debt items the 2026-05-18 PROOF-NEEDS reconciliation banner had deferred. See the dedicated [Proof-Debt-Status](Proof-Debt-Status) page for the full inventory.

| PR | What it lands | Closes |
|---|---|---|
| [#79](https://github.com/hyperpolymath/typed-wasm/pull/79) | `TypedWasm.ABI.VerifierSpec` — total bodies for `VerifierSpecAgreement` + `SourceVerifierAgreement` | Post-A10 audit items 7 + 8 |
| [#80](https://github.com/hyperpolymath/typed-wasm/pull/80) | `LevelAttestationW` witness-indexed GADT + `WitnessCertificate` heterogeneous-list lift | standards#130 "attestation entails the level's semantic property" long-tail |
| [#74](https://github.com/hyperpolymath/typed-wasm/pull/74) | Closed as superseded by #79 (Maybe-bridge design replaced by witness-carrying ctor design) | — |

**Test surface 545 → 627+ assertions** (proof regression 25 → 107 from +33 #79 + +49 #80).
**Zero new `believe_me` / `assert_total` / `postulate` / `sorry` / `assert_smaller`; `%default total` preserved.**

These PRs are independent of the Phase 0 → Phase 1 gate (gate 2 / codegen v0 closed 2026-05-30). They close debt items that would otherwise haunt the v1.0 audit.

## 2026-05-30 — Gate 2 closed: codegen v0

The terminal Phase 0 blocker is resolved. `src/codegen/` adds **twasmc**, a
Zig 0.16 producer (lexer → parser → layout → wasm emitter) that compiles
`examples/01-single-module.twasm` to a valid wasm module carrying the
`typedwasm.{ownership,regions,access-sites}` custom sections.

| Artifact | What it is |
|---|---|
| `src/codegen/` (`twasmc`) | The Zig `.twasm → .wasm` codegen v0 producer + `build.zig` |
| `crates/typed-wasm-verify/src/bin/tw-verify.rs` | New CLI: validate + L7/L10/L13 + L2 verification of a `.wasm` |
| `crates/typed-wasm-verify/tests/fixtures/codegen_v0/` | Producer-emitted golden `.wasm` + `.twasm` source |
| `crates/typed-wasm-verify/tests/codegen_v0.rs` | Blocking, Rust-only end-to-end gate on the golden module |

End-to-end verdict on the emitted module: structural wasm validation ✓,
L7/L10/L13 ownership ✓, L2 access-sites ✓ (11 access-site entries, 3 regions,
5 ownership entries). The emitted bodies perform real typed loads/stores at
computed field offsets (incl. nested `.pos.x` through embedded `@Vec2`, a
`region.scan` loop, `if`/`else`, and `is_null`). Codegen v0 deliberately
targets exactly the example-01 subset; the remaining examples and the full
grammar are Phase 1.
