# TEST-NEEDS: typed-wasm

## CRG Grade: C — ACHIEVED 2026-04-04

## Current State

| Category | Count | Details |
|----------|-------|---------|
| **Source modules** | 21 | 11 Idris2 ABI (Region, TypedAccess, Levels, Pointer, Effects, Lifetime, Linear, MultiModule, Proofs, Tropical, Epistemic), 3 ReScript parser (Ast, Parser, Lexer), 3 Idris2 interface ABI, 2 Zig FFI + cache |
| **Unit tests** | 1 file | ParserTests.res (~82 assertions) |
| **Integration tests** | 0 | None |
| **E2E tests** | 1 | e2e-smoke.mjs (~43 assertions) |
| **Property-based tests** | 1 | property_test.mjs (10 properties, ~40+ assertions) |
| **Benchmarks** | 0 | None |
| **ECHIDNA harness** | 1 | echidna-harness.mjs (7 assertions) |

## What's Missing

### P2P Tests
- [x] **DONE 2026-04-04**: Property-based tests added (`tests/property/property_test.mjs`, 10 properties, ~40+ assertions)
- [ ] No tests for Idris2 ABI type checking with Zig FFI
- [ ] No tests for ReScript parser feeding into Idris2 type checker

### E2E Tests
- [ ] e2e-smoke exists but only 43 assertions for a type system with 10 safety levels
- [ ] No WASM module compilation and execution test
- [ ] No multi-module linking test (MultiModule.idr untested)

### Aspect Tests
- [ ] **Security**: No memory safety violation detection tests (this IS the product's purpose)
- [ ] **Performance**: No benchmarks for type checking overhead vs raw WASM
- [ ] **Concurrency**: No concurrent WASM module compilation tests
- [ ] **Error handling**: No tests for invalid type annotations, malformed WASM

### Build & Execution
- [ ] 11 Idris2 modules with 0 Idris2-level tests -- are proofs checked?
- [ ] Zig FFI integration_test.zig likely a template placeholder

### Benchmarks Needed (CRITICAL)
- [ ] Type checking overhead per WASM instruction
- [ ] Memory region tracking performance
- [ ] Lifetime analysis scaling with module size
- [ ] Comparison: typed-wasm overhead vs raw WASM execution

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
