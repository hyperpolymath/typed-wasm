# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

## Current State

- **LOC**: ~25,000
- **Languages**: ReScript, Idris2, Zig
- **Existing ABI proofs**: Extensive — 11 Idris2 files in `src/abi/TypedWasm/ABI/` covering Effects, Epistemic, Levels, Lifetime, Linear, MultiModule, Pointer, Proofs, Region, Tropical, TypedAccess
- **Dangerous patterns**: None found (comment in Epistemic.idr confirms "no believe_me")

## What Needs Proving

### ReScript Parser Correctness
- `lib/ocaml/Parser.res`, `Lexer.res`, `Ast.res` — WASM text format parser
- Prove: parser produces well-formed ASTs that correspond to valid WASM modules
- Prove: round-trip property (parse . print = id) for the AST

### Multi-Module Safety (src/abi/TypedWasm/ABI/MultiModule.idr)
- Cross-module memory access is the key innovation
- Ensure the existing proofs cover all inter-module pointer dereference cases
- Prove: no module can access memory outside its declared region

### Lifetime / Region Interaction
- `Lifetime.idr` + `Region.idr` — prove that lifetime-scoped regions never outlive their allocator
- This is the highest-value proof target for WASM memory safety

### Tropical Type Semantics (Tropical.idr)
- Tropical semiring operations on types — ensure semiring laws hold
- This may already be partially proven; audit for completeness

### Linear Type Consumption (Linear.idr)
- Prove: every linearly-typed value is consumed exactly once
- This is foundational for the memory safety guarantees

## Recommended Prover

- **Idris2** (already in use with strong proof coverage — deepen and complete)

## Priority

**MEDIUM** — Proof suite is already the most mature in the ecosystem. Focus on completing coverage gaps rather than starting from scratch. The multi-module and lifetime proofs are the highest-value targets.

## Template ABI Cleanup (2026-03-29)

Template ABI removed -- was creating false impression of formal verification.
The removed files (Types.idr, Layout.idr, Foreign.idr) contained only RSR template
scaffolding with unresolved project/author template tokens and no domain-specific proofs.
