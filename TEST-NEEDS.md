# TEST-NEEDS: typed-wasm

## Current State

| Category | Count | Details |
|----------|-------|---------|
| **Source modules** | 21 | 11 Idris2 ABI (Region, TypedAccess, Levels, Pointer, Effects, Lifetime, Linear, MultiModule, Proofs, Tropical, Epistemic), 3 ReScript parser (Ast, Parser, Lexer), 3 Idris2 interface ABI, 2 Zig FFI + cache |
| **Unit tests** | 1 file | ParserTests.res (~82 assertions) |
| **Integration tests** | 0 | None |
| **E2E tests** | 1 | e2e-smoke.mjs (~43 assertions) |
| **Benchmarks** | 0 | None |
| **ECHIDNA harness** | 1 | echidna-harness.mjs (7 assertions) |

## What's Missing

### P2P Tests
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
- **Type safety system with no safety-level-specific tests** -- 10 levels claimed, 0 level-specific test suites
- **11 Idris2 proof modules with 0 proof verification tests** -- "proven" is unproven
- **Tropical.idr and Epistemic.idr (novel type features) have 0 tests** -- research features untested
- **ECHIDNA harness is 7 assertions** -- token gesture, not real verification
- **arXiv potential claimed** -- paper-worthy claims need paper-worthy evidence

## Priority: P0 (CRITICAL)

## FAKE-FUZZ ALERT

- `tests/fuzz/placeholder.txt` is a scorecard placeholder inherited from rsr-template-repo — it does NOT provide real fuzz testing
- Replace with an actual fuzz harness (see rsr-template-repo/tests/fuzz/README.adoc) or remove the file
- Priority: P2 — creates false impression of fuzz coverage
