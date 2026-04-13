# SPDX-License-Identifier: PMPL-1.0-or-later
# typed-wasm Level Achievement Status

## Versioning Scheme (revised 2026-04-13 — typed-wasm-first rollout)

typed-wasm versions track BOTH the highest fully-achieved level tier and the
surface-syntax sugar additions. The rollout now interleaves level work with
consumer-language enablement — see `spec/L13-L16-reserved-syntax.adoc` for the
full trajectory and keyword reservations.

| Version | Levels | Surface | Meaning |
|---------|--------|---------|---------|
| v0.1 | L1-10 | v0.1 grammar | Checked proof core (proofs + runtime L1-6, compile-time L7-10) |
| v1.0 | L1-10 | v0.1 grammar | Audited release of the checked core |
| v1.1 | L1-10 | v0.2 sugar | `const`, `match` on unions, block-expr `if`, split effects `{memory:, caps:}`, `striated` regions. L11-L12 remain draft. |
| v1.2 | L1-10, L13 | v0.3 sugar | +L13 Module isolation: `module Name isolated { ... }`, `private_memory`, `boundary`. Idris2 proof: ModuleIsolation.idr. Surface enforcement: Checker.checkIsolatedModule. |
| v1.3 | L1-10, L13, L14 | v0.4 sugar | +L14 Session protocols: `session Name { state ...; transition consume X -> yield Y; dual : ...; }`. Idris2 proof: SessionProtocol.idr (SessionHandle parameterised by state index, step soundness, DualPair symmetry). Surface enforcement: Checker.checkSession. 63/63 parser tests. |
| **v1.4** | **L1-10, L13, L14, L15** | **v0.5 sugar** | **+L15 Resource capabilities: `capability NAME;` top-level and isolated-module-body declarations; v1.1 `caps: { ... }` sub-clause becomes load-bearing. Idris2 proof: ResourceCapabilities.idr (DistinctCaps L15-A, ContainedIn + containedTrans L15-B, CallCompatible + callCompose L15-C, FullEffectBudget orthogonality with L8). Surface enforcement: Checker.checkCapabilities + scope-threaded checkDeclaration. L15-A (distinct) + L15-B (well-scoped) live at v1.4; L15-C (call-graph monotone) deferred to v1.4.x (proof already carries the theorem). 76/76 parser tests pass.** |
| v1.5 / v2.0 | L1-L16 | v0.2 sugar | +L16 Agent choreography (composition proof over L13+L14+L15) |
| L17 (reserved) | L1-L16, **L17** | future | "Layout-proof striation" with `strided_ptr<T>` — removes the projection-only restriction on striated regions |

**L11 (Tropical)** and **L12 (Epistemic)** remain draft-only at v1.1. They are
orthogonal to the L13-L16 rollout and can promote to checked-in-package at
any intermediate version without blocking the main trajectory. L11 is the
natural home for "striation is cheaper" proofs once it lands.

## v1.1 surface sugar — status

| Feature | Grammar | AST | Lexer | Parser | Checker | Tests |
|---------|---------|-----|-------|--------|---------|-------|
| `const` top-level | spec/grammar.ebnf | Ast.ConstDecl | Const | **TODO** parseConstDecl | Checker.constValueIsLiteral | TODO |
| `match` on union | spec/grammar.ebnf | Ast.MatchStmt | Match | **TODO** parseMatchStmt | Checker.matchIsExhaustive | TODO |
| Block-expr `if` | spec/grammar.ebnf | Ast.BlockIfExpr | Yield | **TODO** parseBlockIfExpr | Checker.blockIfBranchesAgree | TODO |
| Split `effects` | spec/grammar.ebnf | functionDecl.caps | (contextual) | **TODO** parseSplitEffects | (opaque until L15) | TODO |
| `striated` regions | spec/grammar.ebnf | regionDecl.layout | Striated | **DONE** | Checker.striatedLayoutIsWellFormed | TODO |
| Reserved keywords (L13-L16) | spec/L13-L16-reserved-syntax.adoc | — | ReservedKeyword | **TODO** reject at parser | — | TODO |

**AST and lexer tokens landed 2026-04-13. Parser rules and Checker module are
the remaining v1.1 work.**

## Current: checked core = L1-10, L11-L12 = draft, v1.1 surface sugar IN PROGRESS

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
| 13 | Module isolation | ModuleIsolation.idr | (per-module handles, future) | 12 parser/Checker tests | **v1.2 — Idris2 proof + surface checker live; 007 lowering DONE (task #5)** |
| 14 | Session protocols | SessionProtocol.idr | (typed-state handles, future) | 13 parser/Checker tests | **v1.3 — Idris2 proof + surface checker live; 007 send/receive lowering DONE (task #7)** |
| 15 | Resource capabilities | ResourceCapabilities.idr | (future) | 13 parser/Checker tests | **v1.4 — Idris2 proof + surface checker (L15-A + L15-B) live; L15-C call-graph check deferred to v1.4.x; 007 lowering pending (task #9)** |

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
| ModuleIsolation.idr | 0 | 0 | 0 | In package (v1.2 / L13) |
| SessionProtocol.idr | 0 | 0 | 0 | In package (v1.3 / L14) |
| ResourceCapabilities.idr | 0 | 0 | 0 | In package (v1.4 / L15) |
| Proofs.idr | 0 | 0 | 0 | In package |
| Tropical.idr | 0 | 0 | 0 | Draft file; standalone check fails |
| Epistemic.idr | 0 | 0 | 0 | Draft file; standalone check fails |
