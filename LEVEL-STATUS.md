# SPDX-License-Identifier: MPL-2.0
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
| **v1.5** | **L1-10, L13, L14, L15, L16** | **v0.6 sugar** | **+L16 Agent choreography: `choreography { agent_role ...; message ...; composes: L13 + L14 + L15; }`. Idris2 proof: Choreography.idr (composition-only theorem citing lower levels). Surface enforcement: Checker.checkChoreography (L16-A..L16-D). 88/88 parser tests pass.** |
| L17 (reserved) | L1-L16, **L17** | future | "Layout-proof striation" with `strided_ptr<T>` — removes the projection-only restriction on striated regions |

**L11 (Tropical)** and **L12 (Epistemic)** remain draft-only at v1.1. They are
orthogonal to the L13-L16 rollout and can promote to checked-in-package at
any intermediate version without blocking the main trajectory. L11 is the
natural home for "striation is cheaper" proofs once it lands.

## v1.1 surface sugar — status

| Feature | Grammar | AST | Lexer | Parser | Checker | Tests |
|---------|---------|-----|-------|--------|---------|-------|
| `const` top-level | spec/grammar.ebnf | Ast.ConstDecl | Const | **DONE** parseConstDecl (Parser.affine:2088) | Checker.constValueIsLiteral | **DONE** |
| `match` on union | spec/grammar.ebnf | Ast.MatchStmt | Match | **DONE** (Parser.affine:1191) | Checker.matchIsExhaustive | **DONE** |
| Block-expr `if` | spec/grammar.ebnf | Ast.BlockIfExpr | Yield | **DONE** (Parser.affine:529) | Checker.blockIfBranchesAgree | **DONE** |
| Split `effects` | spec/grammar.ebnf | functionDecl.caps | (contextual) | **DONE** parseEffectsClause (Parser.affine:1554) | (opaque until L15) | **DONE** |
| `striated` regions | spec/grammar.ebnf | regionDecl.layout | Striated | **DONE** | Checker.striatedLayoutIsWellFormed | **DONE** |
| Reserved keywords (L13-L16) | spec/L13-L16-reserved-syntax.adoc | — | contextual (per-block) | **DONE** (Parser.affine:2685-2718) | — | **DONE** (v1.4/v1.5 rejection tests) |

**v1.1 surface sugar fully landed: parser, checker, tests all live.
88/88 parser tests pass (verified 2026-04-18). LEVEL-STATUS table was stale
between 2026-04-13 (AST landed) and 2026-04-18 (verification).**

## Current: checked core = L1-10 + L13-L16, L11-L12 = draft

| Level | Name | Idris2 Proof | Zig FFI | Tests | Status |
|-------|------|-------------|---------|-------|--------|
| 1 | Instruction validity | Region.idr | Parser | ECHIDNA 10^5 | **E2E complete** |
| 2 | Region-binding | Region.idr + TypedAccess.idr | Schema lookup | ECHIDNA 10^5 | **E2E complete** |
| 3 | Type-compatible access | TypedAccess.idr | Typed load/store | ECHIDNA 10^5 | **E2E complete** |
| 4 | Null safety | Pointer.idr | Pointer kinds | ECHIDNA 10^5 | **E2E complete** |
| 5 | Bounds-proof | TypedAccess.idr + Levels.idr | Bounds check | ECHIDNA 10^5 | **E2E complete** |
| 6 | Result-type | TypedAccess.idr | Type flow | ECHIDNA 10^5 | **E2E complete** |
| 7 | Aliasing safety | Pointer.idr (Unique) | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased** |
| 8 | Effect-tracking | Effects.idr | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased.  Preorder + composition theorems added A5 (2026-04-18): `subsumeRefl` (alias of `effectSubsumesRefl`), `hasEffectTrans`, `subsumeTrans`, `hasEffectCombineL`/`CombineR`, `subsumePrepend`/`Append`, and the flagship `subsumeCompose` giving `EffectSubsumes d1 a1 -> EffectSubsumes d2 a2 -> EffectSubsumes (d1++d2) (a1++a2)` so L8 attestations compose.** |
| 9 | Lifetime safety | Lifetime.idr | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased.  Preorder + load-safety theorems added A4 (2026-04-18): `outlivesRefl`, `outlivesTrans` (alias of pre-existing `outlivesTransitive` with 7-constructor case analysis), `loadSafe` proof-term, behavioural lemmas `loadSafeOffset` and `loadSafeIrrelevant` (proof irrelevance at the value level).** |
| 10 | Linearity | Linear.idr (QTT q=1) | Erased (QTT) | ECHIDNA 10^4 | **Proven [sfap], erased.  Propositional state-machine theorems added A3 (2026-04-18): distinctUsage, consumePreservesData, noReuse, noReuseEcho — usage-indexed handle `LinHandleU Fresh/Consumed tok` with `consume` state transition, alongside the QTT structural layer.** |
| 11 | Tropical cost-tracking | Tropical.idr | Not yet | None | **In package (A1, 2026-04-18).  Commutative-semiring closure PROVEN (A2, 2026-04-18): all 12 axioms — tropAddLeftId/RightId/Comm/Assoc, tropMulLeftId/RightId/Comm/Assoc, tropMulLeftAnn/RightAnn, tropMulDistrib/DistribR.  Uses structural `tropMin` (007-lang template).  Zero dangerous patterns.** |
| 12 | Epistemic safety | Epistemic.idr | Not yet | None | **In package (A1, 2026-04-18); A10 (2026-05-26) closes the previously-deferred "freshness propagation under concurrent writes" gap with the flagship `freshnessPropagatesUnderWrites` plus the supporting `concurrentWriteStales`, `resyncRecoversFresh`, `freshNotStale`, `freshImpliesEqual`, `staleImpliesLT`, `syncChainEndsFresh`, and the `epistemicFreshness` projector (closes PROOF-NEEDS §P1.2 "Level12Proof implies freshness"). 11 named theorems total.** |
| 13 | Module isolation | ModuleIsolation.idr | (per-module handles, future) | 12 parser/Checker tests | **v1.2 — Idris2 proof + surface checker live; 007 lowering DONE (task #5)** |
| 14 | Session protocols | SessionProtocol.idr | (typed-state handles, future) | 13 parser/Checker tests | **v1.3 — Idris2 proof + surface checker live; 007 send/receive lowering DONE (task #7)** |
| 15 | Resource capabilities | ResourceCapabilities.idr | (future) | 13 parser/Checker tests | **v1.4 — Idris2 proof + surface checker (L15-A + L15-B) live; L15-C call-graph check deferred to v1.4.x; 007 lowering DONE (task #9)** |
| 16 | Agent choreography | Choreography.idr | (future) | 12 parser/Checker tests | **v1.5 — composition proof over L13+L14+L15 live; surface checker enforces L16-A (role targets exist), L16-B (message endpoints declared), L16-C (payload primitive/declared region ref), L16-D (exact `L13 + L14 + L15` composition spec).** |

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

Levels 11-12 are draft for surface semantics, not for ipkg membership.
As of 2026-04-18 (commit A1) both `Tropical.idr` and `Epistemic.idr` are
in `typed-wasm.ipkg` and build clean under Idris2 0.8.0 — see the
2026-05-18 reconciliation in `PROOF-NEEDS.md`. The "draft" label
applies to the level semantics themselves (Tropical cost-tracking and
Epistemic freshness propagation under concurrent writes remain
research-grade): theorems live, but the surface language and Zig FFI
do not yet expose them. Wiring these levels through the rest of the
toolchain remains future work.

## Proof inventory

| File | believe_me | postulate | assert_total | Checked status |
|------|-----------|-----------|--------------|----------------|
| Region.idr | 0 | 0 | 0 | In package.  Structural injectivity added A8 (2026-04-18): `fieldNameInj` / `fieldTypeInj` / `fieldInj` (MkField constructor injectivity), `schemaEqSym` / `schemaEqTrans` (making SchemaEq a full equivalence relation with the pre-existing `schemaEqRefl`), `lookupFieldName` (L2 soundness — `FieldIn name schema` implies `fieldName (lookupField prf) = name`).  A12 (2026-05-26): byte-disjointness layer added — `RegionDisjoint r1 r2` (two constructors covering both orderings of footprint endpoints) plus `regionDisjointSym` proving symmetry.  Closes post-A10 audit item 6.  Cross-level theorem linking disjointness to L7 aliasing-safety and L10 linearity deferred to a future pass. |
| TypedAccess.idr | 0 | 0 | 0 | In package |
| Levels.idr | 0 | 0 | 0 | In package |
| Pointer.idr | 0 | 0 | 0 | In package |
| Effects.idr | 0 | 0 | 0 | In package |
| Lifetime.idr | 0 | 0 | 0 | In package |
| Linear.idr | 0 | 0 | 0 | In package |
| MultiModule.idr | 0 | 0 | 0 | In package.  Flagship no-spoofing theorem proven A6 (2026-04-18): `FieldMatches`, `SchemaSub` preorder (`schemaSubRefl`, `schemaSubTrans`), `ModuleCompat` indexed on modules + schemas (`compatRefl`, `compatTrans`), and the flagship `noSpoofing : ModuleCompat from to imp exp -> FieldMatches f imp -> FieldMatches f exp`.  Worked Rust-exports / AffineScript-imports example (4-field export, 2-field import subset) constructs a live certificate and applies the theorem.  A10 (2026-05-26) closes the deferred `compatCommute` item: mutual-subschema commutativity `compatCommute : ModuleCompat from to imp exp -> SchemaSub exp imp -> ModuleCompat to from exp imp`, plus the `noSpoofingBidir` corollary returning a pair of field-transport functions.  Second worked example (`serviceA`/`serviceB` with permuted schemas) demonstrates `compatCommute` on a case where both `SchemaSub` directions hold. |
| ModuleIsolation.idr | 0 | 0 | 0 | In package (v1.2 / L13) |
| SessionProtocol.idr | 0 | 0 | 0 | In package (v1.3 / L14) |
| ResourceCapabilities.idr | 0 | 0 | 0 | In package (v1.4 / L15).  A12 (2026-05-26): `containedConcat` proves `ContainedIn` distributes over `++`; `jointBudgetCompose` proves the L8 ↔ L15 **joint** budget composition theorem — given individual `EffectSubsumes` witnesses and individual `FunctionCaps` witnesses for two functions sharing an owner module, the compound function still satisfies both the combined L8 envelope (via `subsumeCompose`) AND the combined L15 module envelope (via `containedConcat` + `l15bSoundness`).  Closes post-A10 audit item 3. |
| Choreography.idr | 0 | 0 | 0 | In package (v1.5 / L16) |
| Proofs.idr | 0 | 0 | 0 | In package.  Attestation API hardened A7 (2026-04-18): every L1-L10 attestation now requires a witness from its level module (Schema / FieldIn / WasmTypeCompat / Ptr-NonNull / InBounds / AccessResult / ExclusiveWitness / EffectSubsumes / Lifetime.Outlives / CompletedProtocol).  `simpleReadCert` / `fullCert12` / `fullCert15` thread witnesses per level; the certificate cannot be constructed without real proof artefacts.  Level-achievement layer added A8 (2026-04-18): `LevelAchievedIn` predicate, `achievedAppendL` / `achievedAppendR` list-append preservation, `LevelAchieved n cert` lifted to certificates, `composeAchievedL` / `composeAchievedR` proving any level achieved in either component of `composeCertificates` is still achieved in the composition.  A11 (2026-05-26): partial laws for `composeCertificates` itself — `achievedAppendSplit` decomposes a `LevelAchievedIn n (xs ++ ys)` into one side; `composeAssocLists` proves the list-level associativity of three-way composition; `composeAchievedSym` is the symmetric counterpart of `composeAchievedL`/`R`, recovering the achieved-side from a composed certificate.  A12 (2026-05-26): switched `composeCertificates` from Ord-derived `Prelude.min` to structural `Data.Nat.minimum` so structural lemmas apply; **full** `composeAssoc` proves three-way associativity across list parts, multi-module parts, AND `highestProven` Nat side (via `minimumAssociative`); `composeHighProvenComm` proves Nat-side commutativity (via `minimumCommutative`).  Closes post-A10 audit item 4 in full. |
| Tropical.idr | 0 | 0 | 0 | In package (A1, 2026-04-18) |
| Epistemic.idr | 0 | 0 | 0 | In package (A1, 2026-04-18).  A10 (2026-05-26): propagation theorems added — `freshImpliesEqual`, `staleImpliesLT`, `freshNotStale` (mutual exclusion via local `ltIrreflexive`), `concurrentWriteStales`, `resyncRecoversFresh`, the flagship `freshnessPropagatesUnderWrites`, `syncChainEndsFresh`, and the `epistemicFreshness` projector on `Level12Proof` (closes PROOF-NEEDS §P1.2).  A11 (2026-05-26): constructor-tightening pass — `WriteSync` now demands a `FieldVersion` witness with three equality components (`field`/`version`/`lastWriter`), and `Knowledge.Observed` is grounded in a `Sync` event (no more unfounded versions).  Corollaries: `writeSyncIdentifiesWriter` returns the `FieldVersion` (+ the three projections) for an explicit-or-implicit Sync; `observedHasProvenance` extracts the witnessing prior-version and `Sync` from any `Observed` value. |
| Echo.idr | 0 | 0 | 0 | In package (A0, 2026-04-18) |

## Post-codegen verifier (Rust)

The Idris2 proofs above establish that **the type discipline is sound** —
L1-L10 (and L13-L16) are mechanically verified at the spec level. They
say nothing about whether a particular wasm module out of a particular
codegen actually obeys the discipline.

`crates/typed-wasm-verify/` (added 2026-05-15) closes that loop on the
**post-codegen** side. Given a wasm module plus an
`typedwasm.ownership` custom section, the crate runs a per-path
`(min, max)` use-range analysis over every function body and reports
L7 (aliasing) + L10 (linearity) violations. It's a second line of
defence: the source-level checker enforces the rules during compilation;
this crate re-checks them on the emitted IR to catch codegen bugs.

| Layer | What it proves | Where |
|-------|----------------|-------|
| Idris2 proofs | Type discipline is sound (spec-level) | `src/abi/TypedWasm/ABI/*.idr` |
| Source checker | Source program respects discipline | `hyperpolymath/affinescript:lib/codegen.ml` (QTT pass), upcoming `.twasm` parser/checker |
| **Post-codegen verifier** | **Emitted wasm respects discipline** | **`crates/typed-wasm-verify/` (Rust)** + `hyperpolymath/affinescript:lib/{tw_verify,tw_interface}.ml` (OCaml, reference impl) |

The Rust crate is a faithful port of the OCaml reference; the OCaml
files remain the spec of record until the cross-compat suite at
`crates/typed-wasm-verify/tests/cross_compat.rs` is supplemented with
real affinescript-emitted fixtures (deferred work, "C5.1").

**Coverage:** L7 (ExclBorrow) + L10 (Linear) only.
L1-L6, L13-L16 enforcement on emitted wasm is future work.

**Consumers** (live as of 2026-05-15):

- `hyperpolymath/ephapax:src/ephapax-wasm/` — emits the
  `typedwasm.ownership` section on every compile
- `hyperpolymath/ephapax:src/ephapax-cli/` — exposes the verifier via
  `ephapax compile --verify-ownership`
