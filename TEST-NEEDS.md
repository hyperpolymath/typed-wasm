# TEST-NEEDS: typed-wasm

## CRG Grade: C — ACHIEVED 2026-04-04

## Current State

| Category | Count | Details |
|----------|-------|---------|
| **Source modules** | 21 | 11 Idris2 ABI (Region, TypedAccess, Levels, Pointer, Effects, Lifetime, Linear, MultiModule, Proofs, Tropical, Epistemic), 4 AffineScript parser (Ast, Parser, Lexer, Checker), 3 Idris2 interface ABI, 2 Zig FFI + cache, 1 Rust verifier crate (typed-wasm-verify, ~1.6k LOC + 53 tests) |
| **Unit tests** | 2 files | ParserTests.affine (88 assertions), crates/typed-wasm-verify (43 unit + 10 cross-compat) |
| **Integration tests** | 1 | tests/contracts/airborne-step-state-contract.mjs (14 assertions) |
| **E2E tests** | 2 | tests/smoke/e2e-smoke.mjs (40 assertions), tests/e2e/e2e-driver.mjs (corpus driver) |
| **Per-level tests** | 10 | tests/levels/L1.mjs .. L10.mjs (56 assertions total) |
| **Aspect tests** | 2 | tests/aspect/claim-envelope.mjs (49 assertions — added 2026-05 to catch cross-doc claim drift after deep audit found 5 such drifts), tests/aspect/security-envelope.mjs (10 assertions — added 2026-05-24 to catch SECURITY.md/security.txt drift, SPDX gaps, badge-vs-reality, committed secrets) |
| **Property-based tests** | 1 | tests/property/property_test.mjs (29 assertions across 6 invariants P1-P6: parser determinism, comment stability, diagnostic positional consistency, example-corpus liveness, level-fixture coverage, 5-trial stability — added 2026-05-24, closes the 2026-04-04 ghost) |
| **Proof regression** | 1 | tests/proof/regression.mjs (25 named-theorem presence assertions + optional idris2 --check layer — added 2026-05-24) |
| **Benchmarks** | 1 | benchmarks/parser-bench.mjs (per-example wallclock; median/p95/min/throughput; JSON summary on stderr; added 2026-05) |
| **ECHIDNA harness** | 1 | tests/echidna/echidna-harness.mjs (659 LOC, 124 local assertions, remote prover-wars submission) |

## What's Missing

### P2P Tests
- [x] **DONE 2026-05-24**: `tests/property/property_test.mjs` exists with
      29 assertions across 6 invariants (parser determinism, comment
      stability, diagnostic positional consistency, example-corpus
      liveness, level-fixture coverage, 5-trial stability). Wired into
      Justfile `test-property` and CI smoke job. Closes the revoked
      2026-04-04 ghost entry.
- [ ] No tests for Idris2 ABI type checking with Zig FFI
- [ ] No tests for AffineScript parser feeding into Idris2 type checker

### E2E Tests
- [x] **DONE 2026-05**: `tests/e2e/e2e-driver.mjs` exercises every
      example through parse + check with skip/expect-clean/expect-diagnostic
      pragmas. Smoke test still narrow (40 assertions) but now augmented
      by the per-level suite (56 more) and the aspect test (49 more).
- [ ] No WASM module compilation and execution test (blocked on codegen)
- [ ] No multi-module linking test (MultiModule.idr untested at runtime)

### Aspect Tests
- [x] **DONE 2026-05**: `tests/aspect/claim-envelope.mjs` — 49 checks that
      cross-document claims (README/ROADMAP/LEVEL-STATUS/EXPLAINME) stay
      consistent with actual artefacts (ipkg, Rust constants, CI pins,
      example corpus, RSR surface). Built in response to a deep audit
      finding five drifts the test now catches.
- [x] **DONE 2026-05-24** (security claim-envelope dimension):
      `tests/aspect/security-envelope.mjs` — 10 assertions covering
      SECURITY.md ↔ .well-known/security.txt contact alignment,
      disclosure-timeline concreteness, SPDX-header presence on all
      git-tracked source files, README badge-claim-vs-reality (parses
      Idris2 comments out before substring matching), no committed
      credential patterns, LICENSE-vs-SPDX consistency. Caught two real
      bugs in the same commit it was added: template residue in
      `.well-known/security.txt` and missing SPDX on three files.
- [ ] **Security (behavioural)**: No memory safety violation detection
      tests at the verifier-rejects-bad-program level beyond what
      `tests/levels/L*.mjs` covers (10/10 per-level negative cases
      exist). Reaching full safety-violation coverage is a Phase 1
      deliverable since it requires end-to-end codegen.
- [ ] **Performance**: see Benchmarks below
- [ ] **Concurrency**: No concurrent WASM module compilation tests
- [ ] **Error handling**: 10/10 per-level test suites (`tests/levels/L*.mjs`)
      include negative cases — partial coverage

### Build & Execution
- [x] **PARTIAL 2026-05-24**: `tests/proof/regression.mjs` provides
      Layer 1 (named-theorem presence) — 25 assertions covering Region,
      TypedAccess, Levels, Linear, Lifetime, Effects, Pointer,
      MultiModule, Layout, Proofs. Catches silent theorem deletion or
      rename. Layer 2 (`idris2 --check typed-wasm.ipkg`) runs only when
      idris2 is on PATH, falls back to skip otherwise; pass `--strict`
      to require idris2. The strong test still depends on the toolchain
      being installable in CI, which is its own Phase 0 item.
- [ ] Zig FFI integration_test.zig likely a template placeholder

### Benchmarks
- [x] **DONE 2026-05**: `benchmarks/parser-bench.mjs` — per-example parse +
      check wallclock with median / p95 / min / throughput and JSON summary
      for trend tracking. Only the parser is end-to-end today, so that's
      where benchmark evidence has to start.
- [ ] Type-checking overhead per WASM instruction (blocked on codegen +
      Zig FFI runtime path)
- [ ] Memory region tracking performance (blocked on codegen)
- [ ] Lifetime analysis scaling with module size (blocked on codegen)
- [ ] Comparison: typed-wasm overhead vs raw WASM execution
      (blocked on codegen)

### Self-Tests
- [ ] No type system self-consistency check

## FLAGGED ISSUES
- **Type safety system with no safety-level-specific tests** -- 10 levels claimed, 0 level-specific test suites (IN PROGRESS 2026-04-18 — L1-L3 pilot + agent handoff for L4-L10)
- **11 Idris2 proof modules with 0 proof verification tests** -- "proven" is unproven. Update 2026-04-18: A3-A9 theorems landed in commits 987930c, c896a44, 3097b50, 9ebe867 (injectivity, level-achievement monotonicity, erasure P3.1, QTT witness, witness-requiring attestations). L7-L10 preorder + composition lemmas now live. Full per-level Idris2 test files still absent.
- **Tropical.idr and Epistemic.idr (novel type features) have 0 tests** -- research features untested (L11 semiring closure proven A2 2026-04-18 but no dedicated test suite)
- ~~**ECHIDNA harness is 7 assertions** -- token gesture, not real verification~~ SUPERSEDED 2026-04-18: tests/echidna/echidna-harness.mjs is now 659 LOC with a random-program generator, 36 proof obligations per run, and parse-rate measurement.
- **arXiv potential claimed** -- paper-worthy claims need paper-worthy evidence

## Priority: P0 (CRITICAL)

## FAKE-FUZZ ALERT — RESOLVED 2026-04-18

- ~~`tests/fuzz/placeholder.txt` is a scorecard placeholder inherited from rsr-template-repo — it does NOT provide real fuzz testing~~ RESOLVED. The placeholder file is gone; `tests/fuzz/README.adoc` is now an honest status marker pointing at `tests/echidna/echidna-harness.mjs` (659 LOC, real random-program fuzz) and `ffi/zig/test/`. A dedicated retained fuzz corpus is still future work.
- Replace with an actual fuzz harness (see rsr-template-repo/tests/fuzz/README.adoc) or remove the file
- Priority: P2 — creates false impression of fuzz coverage
