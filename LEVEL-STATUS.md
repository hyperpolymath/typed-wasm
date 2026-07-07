# SPDX-License-Identifier: CC-BY-SA-4.0
<!-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
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
| 11 | Tropical cost-tracking | Tropical.idr | Not yet | None | **In package (A1, 2026-04-18).  Commutative-semiring closure PROVEN (A2, 2026-04-18): all 12 axioms.  Uses structural `tropMin` (007-lang template).  Zero dangerous patterns.  A16 (2026-06-16) estate accommodation: added the canonical dioid ORDER layer (`tropLe` refl/trans + add/mul monotonicity, mirrors `tropical-resource-typing` `Resource.Algebra.Ordered`), the MinMax BOTTLENECK layer (`tropMax` + `hubCeiling`, mirrors `Resource.Instances.MinMax` + `Bridge.hub_ceiling_le`), `ResidueMeasure` (E→R, mirrors `Resource.EchoBridge`), and `Level11BottleneckProof` + `bottleneckCeilsEdges` wired into `Proofs.attestL11_Bottleneck`/`_Sound`.** |
| 12 | Epistemic safety | Epistemic.idr | Not yet | None | **In package (A1, 2026-04-18); A10 (2026-05-26) closes the "freshness propagation under concurrent writes" gap with `freshnessPropagatesUnderWrites` + supporting theorems (11 total; closes PROOF-NEEDS §P1.2).  A15 (2026-06-16) estate accommodation: ADDITIVE `syncGrade` layer reusing sibling `Tropical.TropCost` (∞ = never-synced) + `neverSyncedInfeasible`/`observedFeasible`/`observedNotInfeasible` — extant Nat-indexed proofs untouched.  Header IS-NOT note: this read-consistency model is a DIFFERENT problem from canonical `epistemic-types`' standpoint-indexed modality.** |
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
| Region.idr | 0 | 0 | 0 | In package.  Structural injectivity added A8 (2026-04-18): `fieldNameInj` / `fieldTypeInj` / `fieldInj` (MkField constructor injectivity), `schemaEqSym` / `schemaEqTrans` (making SchemaEq a full equivalence relation with the pre-existing `schemaEqRefl`), `lookupFieldName` (L2 soundness — `FieldIn name schema` implies `fieldName (lookupField prf) = name`).  A12 (2026-05-26): byte-disjointness layer added — `RegionDisjoint r1 r2` (two constructors covering both orderings of footprint endpoints) plus `regionDisjointSym` proving symmetry.  Closes post-A10 audit item 6.  A13 (2026-05-26): byte-separation cross-level layer added — `RegionsOverlap r1 r2` (an address inside both region footprints), `disjointImpliesNoOverlap` proving `RegionDisjoint r1 r2 -> Not (RegionsOverlap r1 r2)`, plus `regionsOverlapSym`.  Closes the L7/L10 cross-level link explicitly deferred at A12. |
| TypedAccess.idr | 0 | 0 | 0 | In package |
| Levels.idr | 0 | 0 | 0 | In package |
| Pointer.idr | 0 | 0 | 0 | In package |
| Effects.idr | 0 | 0 | 0 | In package |
| Lifetime.idr | 0 | 0 | 0 | In package |
| Linear.idr | 0 | 0 | 0 | In package |
| MultiModule.idr | 0 | 0 | 0 | In package.  Flagship no-spoofing theorem proven A6 (2026-04-18): `FieldMatches`, `SchemaSub` preorder (`schemaSubRefl`, `schemaSubTrans`), `ModuleCompat` indexed on modules + schemas (`compatRefl`, `compatTrans`), and the flagship `noSpoofing : ModuleCompat from to imp exp -> FieldMatches f imp -> FieldMatches f exp`.  Worked Rust-exports / AffineScript-imports example (4-field export, 2-field import subset) constructs a live certificate and applies the theorem.  A10 (2026-05-26) closes the deferred `compatCommute` item: mutual-subschema commutativity `compatCommute : ModuleCompat from to imp exp -> SchemaSub exp imp -> ModuleCompat to from exp imp`, plus the `noSpoofingBidir` corollary returning a pair of field-transport functions.  Second worked example (`serviceA`/`serviceB` with permuted schemas) demonstrates `compatCommute` on a case where both `SchemaSub` directions hold. |
| ModuleIsolation.idr | 0 | 0 | 0 | In package (v1.2 / L13).  A13 (2026-05-26): L13×L10 cross-level layer added — imports `Linear`, exposes `LinearAcrossBoundary from to regName bs token` (an L13 `AccessWitness` paired with an L10 `LinHandle`) plus accessors `acrossWitness` / `acrossHandle`, the no-bypass theorem `linearTransferRequiresBoundary` (any non-local linear-handle transfer requires a concrete boundary in `bs`, proved by reusing `crossAccessImpliesBoundary`), and `linearTransferLocal` (local-case constructor).  Closes post-A10 audit item 5a. |
| SessionProtocol.idr | 0 | 0 | 0 | In package (v1.3 / L14).  A13 (2026-05-26): L14×L13 cross-level layer added — imports `ModuleIsolation`, exposes `SessionAcrossBoundary from to proto state regName bs` plus accessors, `sessionAcrossPreservesState` (the state index survives the transfer), `sessionTransferRequiresBoundary` (no-bypass, same shape as the L10 version one level up), and `sessionTransferLocal`.  Closes post-A10 audit item 5b. |
| ResourceCapabilities.idr | 0 | 0 | 0 | In package (v1.4 / L15).  A12 (2026-05-26): `containedConcat` proves `ContainedIn` distributes over `++`; `jointBudgetCompose` proves the L8 ↔ L15 **joint** budget composition theorem — given individual `EffectSubsumes` witnesses and individual `FunctionCaps` witnesses for two functions sharing an owner module, the compound function still satisfies both the combined L8 envelope (via `subsumeCompose`) AND the combined L15 module envelope (via `containedConcat` + `l15bSoundness`).  Closes post-A10 audit item 3. |
| Choreography.idr | 0 | 0 | 0 | In package (v1.5 / L16) |
| Proofs.idr | 0 | 0 | 0 | In package.  Attestation API hardened A7 (2026-04-18): every L1-L10 attestation now requires a witness from its level module (Schema / FieldIn / WasmTypeCompat / Ptr-NonNull / InBounds / AccessResult / ExclusiveWitness / EffectSubsumes / Lifetime.Outlives / CompletedProtocol).  `simpleReadCert` / `fullCert12` / `fullCert15` thread witnesses per level; the certificate cannot be constructed without real proof artefacts.  Level-achievement layer added A8 (2026-04-18): `LevelAchievedIn` predicate, `achievedAppendL` / `achievedAppendR` list-append preservation, `LevelAchieved n cert` lifted to certificates, `composeAchievedL` / `composeAchievedR` proving any level achieved in either component of `composeCertificates` is still achieved in the composition.  Attestation soundness A9 (2026-05-18): per-level `attestLN_Sound` family proving `LevelAchievedIn N [attestLN_X w]` — the weak "certificate claims level N" face.  A11 (2026-05-26): partial laws for `composeCertificates` — `achievedAppendSplit`, `composeAssocLists`, `composeAchievedSym`.  A12 (2026-05-26): switched `composeCertificates` from Ord-derived `Prelude.min` to structural `Data.Nat.minimum`; **full** `composeAssoc`; `composeHighProvenComm`.  Closes post-A10 audit item 4 in full.  **Witness-indexed redesign 2026-05-27 (PR #80, closes standards#130 long-tail)**: `LevelAttestationW : (n : Nat) -> Type` GADT with one ctor per level packaging the actual witness; 15 `attestLNW_*` smart ctors; 15 `attestLNW_Entails<Property>` extractors (a consumer holding `LevelAttestationW 7` can now discharge L7 alias-freeness via `ExclusiveWitness s`, not just the weak claim-predicate); `toLegacy` bridge; 15 round-trip `Refl`s; uniform `attestLW_AchievedIn` subsuming the A9 family.  **`WitnessCertificate` lift 2026-05-27 (PR #80, folded from #83)**: existential `SomeAttestationW` wrapper, `record WitnessCertificate` mirror of `ProofCertificate` with witness-carrying levels, `witnessToLegacy` bridge, `composeWitness` mirror, `composeWitnessLegacyAgree` compat lemma, `WitnessAchieved` predicate. |
| Tropical.idr | 0 | 0 | 0 | In package (A1, 2026-04-18) |
| Epistemic.idr | 0 | 0 | 0 | In package (A1, 2026-04-18).  A10 (2026-05-26): propagation theorems added — `freshImpliesEqual`, `staleImpliesLT`, `freshNotStale` (mutual exclusion via local `ltIrreflexive`), `concurrentWriteStales`, `resyncRecoversFresh`, the flagship `freshnessPropagatesUnderWrites`, `syncChainEndsFresh`, and the `epistemicFreshness` projector on `Level12Proof` (closes PROOF-NEEDS §P1.2).  A11 (2026-05-26): constructor-tightening pass — `WriteSync` now demands a `FieldVersion` witness with three equality components (`field`/`version`/`lastWriter`), and `Knowledge.Observed` is grounded in a `Sync` event (no more unfounded versions).  Corollaries: `writeSyncIdentifiesWriter` returns the `FieldVersion` (+ the three projections) for an explicit-or-implicit Sync; `observedHasProvenance` extracts the witnessing prior-version and `Sync` from any `Observed` value. |
| Echo.idr | 0 | 0 | 0 | In package (A0, 2026-04-18).  A16 (2026-06-16) estate accommodation: header re-characterised to the accurate echo-types definition — a **tropically-graded modality of structured information loss** (grade = min-plus = `Tropical.TropCost` = irrecoverability), exact-on-a-fiber recoverability; monad/comonad/adjunction VARIANCE explicitly deferred to upstream `--safe` Agda (cf echo-types RETRACTION R-2026-05-18 + experimental R0–R4).  Added `EchoR` + `echoToResidue` (mirrors `echo-types` `EchoResidue.agda`; an attestation = a retained residue).  Categorical base remains the settled fiber/slice structure. |
| VerifierSpec.idr | 0 | 0 | 0 | Introduced A13 (2026-05-26, PR #72) as statement-level spec-of-record for post-A10 items 7+8.  **Promoted to total bodies 2026-05-27 (PR #79)**: same `ModuleSummary` / `FunctionSummary` / `OwnershipIntent` shapes, plus structural acceptance predicates `TokenFresh` / `IntentsLinearAcceptable` / `FunctionsAccepted`, the three acceptance predicates `SpecAccepts` / `VerifierAccepts` / `SourceAccepts` (the latter two carry a `TrustedFixture` inline so the differential ctor still terminates in a structural witness), the two **agreement records `VerifierSpecAgreement` (item 7) and `SourceVerifierAgreement` (item 8)** with totally-proven bodies, concrete inhabitants `verifierSpecAgreement` / `sourceVerifierAgreement` (the first total no-`believe_me` agreement values in the codebase), end-to-end composition lemmas `sourceImpliesSpec` / `specImpliesSource` and `*Concrete` specialisations, demo modules (empty / `allocFreeModule` / `allocFreeWithBorrowModule` / `fixtureCleanLinearConsumerModule` mirrored from cross_compat row 1), and four discrimination proofs (`notSpecAcceptsBadDoubleConsume`, `notVerifierAcceptsBadDoubleConsume` ruling out BOTH ctors, `notSourceAcceptsBadDoubleConsume` ruling out BOTH ctors, `notSpecAcceptsBadDoubleProduce`) showing L10 has teeth and the differential escape hatch cannot smuggle a bad module past the verifier. |

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

The Rust crate + Idris2 `VerifierSpec.idr` are the **spec of record**
(ADR-0008, 2026-07-07); the OCaml files are a conforming
implementation. The synthetic-fixture cross-compat
suite at `crates/typed-wasm-verify/tests/cross_compat.rs` is the
parity oracle; **C5.1** (`tests/cross_compat_real.rs`, landed
2026-05-27 via PR #81) cross-checks it against real
`affinescript`-emitted bytes (4-fixture corpus, regenerate workflow
pins affinescript SHA for drift detection).

**Coverage** (2026-05-27):

| Level | Enforced on emitted wasm? | Where |
|-------|---------------------------|-------|
| L7 (aliasing) | **YES** | `verify_function` per-path use-range |
| L10 (linearity) | **YES** | `verify_function` per-path use-range |
| L13 (module isolation, negative form) | **YES** | `verify_from_module`, gated on ownership-section presence (PR #37, 2026-05-19) |
| L13 (cross-module schema agreement, positive form) | **YES (import-bound, carrier-backed)** | `typedwasm.region-imports` carrier — proposal 0003 `[accepted]` 2026-07-07 → ADR-0007; `verify_region_imports_from_module` (module-local) + `verify_link_graph` (cross-module `SchemaSub` → `CompatCertificate`s); gated `cargo feature = "unstable-l13-imports"`; in-tree producer emits from `import region … from "…" { … }` source (`tests/example02.rs`) |
| L2 (region binding) | **YES** (carrier-backed) | `verify_access_sites_from_module` PR #109; reads `typedwasm.regions` + `typedwasm.access-sites` (proposals 0001 + 0002 `[accepted]` 2026-05-30; codec PR #107; gated `cargo feature = "unstable-l2"`) |
| L3–L6 (type-compat, null, bounds, result-type) | **YES** (carrier-backed, schema half) | `typedwasm.regions` codec PR #107; cross-checks against `Region.idr::WasmType`, `Pointer.idr::Nullability`, cardinality. Per-access enforcement gated on producer codegen of access-sites (`affinescript#462`, `ephapax#251`). |
| L15 (resource capabilities, L15-A/B) | **YES** (carrier-backed) | `verify_capabilities_from_module` PR #109; reads `typedwasm.capabilities` (proposal 0001 `[accepted]`; codec PR #107; gated `cargo feature = "unstable-l15"`). L15-C deferred to proposal 0004 `[draft]`. |
| L14, L16 | **out of scope** | Gated on AffineScript surface work (no `session`/`choreography` producer emission yet) |

**Open gating items** (post proposals 0001 + 0002 acceptance, 2026-05-30):

1. **Producer codegen** — verifier passes ship; producer-side emission
   lags. See proposal 0001 §"Appendix B — Producer-readiness checklist"
   for IR prerequisites of each carrier. Tracking:
   `affinescript#444` (Tw_section dedup, ✅ merged), `affinescript#462`
   (access-sites codegen, open), `ephapax#221` (Ty::Borrow surfacing,
   open), `ephapax#251` (access-sites codegen, filed 2026-05-30),
   `ephapax#250` (Codegen dead-fields cleanup, ✅ merged 2026-05-30).
2. **L13 cross-module (positive form)** — DONE in-tree (2026-07-07):
   proposal 0003 `[accepted]` → ADR-0007; codec + `verify_link_graph`
   behind `unstable-l13-imports`; in-tree producer emits from source.
   Sibling-producer adoption (AffineScript Roadmap C3 / Ephapax)
   tracked by cross-repo issues.
3. **L15-C (call-graph monotonicity)** — proposal 0004 `[draft]`
   (`docs/proposals/0004`). Gated on producer-side L15-A emission
   (Roadmap C2 not started in either producer).
4. **ADR promotion** — DONE (2026-05-30): proposals 0001 + 0002
   promoted to `docs/decisions/0002-multi-producer-carrier-sections.adoc`
   (ADR-0002) and `docs/decisions/0003-access-site-carrier.adoc`
   (ADR-0003). Proposal files retained as canonical wire-format
   references.

**Spec-of-record alignment (2026-05-27, PR #79).**  The
`TypedWasm.ABI.VerifierSpec` Idris2 module now states the
**verifier ↔ spec ↔ source** agreement as totally-proven
inhabitants of two records (`VerifierSpecAgreement`,
`SourceVerifierAgreement`).  Closes the multi-week residual flagged
by PR #74 ("Items 7 + 8 stated as obligations" from PR #72).  The
Rust verifier's accept-verdicts on differential-harness fixtures are
modelled via `TrustedFixture m` values that package the structural
witness inline — the trust-injection moment is `MkTrustedFixture`
construction (single grep point for audit).  A drift between this
module and the Rust verifier's behaviour now shows up as either a
failing differential-harness fixture or as an absent
`TrustedFixture` registration.

**Consumers** (live as of 2026-05-15):

- `hyperpolymath/ephapax:src/ephapax-wasm/` — emits the
  `typedwasm.ownership` section on every compile
- `hyperpolymath/ephapax:src/ephapax-cli/` — exposes the verifier via
  `ephapax compile --verify-ownership`

## Estate-axis accommodation (A15/A16 — 2026-06-16)

An adversarially-verified audit (idris2 ground-truth) found that L11/L12 and
the Echo module were internally sound and compiling but **not accommodated** to
the canonical estate repos — each had been sourced/ported from somewhere *other*
than the canonical repo (Tropical from `007-lang`, Echo from a dead
`~/Desktop/EchoFibers.agda`, Epistemic independently reinvented), with stale or
absent cross-references. This is the estate boundary-erosion pattern. The
following accommodation work landed **local, unpushed, all type-checking under
idris2 0.8.0** (`%default total`, no `believe_me`); the full `typed-wasm.ipkg`
package builds green (22 modules):

| Axis | Canonical repo | Accommodation |
|------|----------------|---------------|
| L11 Tropical | `tropical-resource-typing` (Lean4 `Resource.*`) @ `2e35229` | cross-doc fixed (was stale `f6c5a6f`, Isabelle-only); added `tropLe` dioid order (refl/trans/monotonicity ~ `Resource.Algebra.Ordered`), `tropMax` MinMax bottleneck + `hubCeiling` (~ `Resource.Instances.MinMax` + `Bridge.hub_ceiling_le`), `ResidueMeasure` (~ `Resource.EchoBridge`), `Level11BottleneckProof` + `bottleneckCeilsEdges` wired into `Proofs.attestL11_Bottleneck`/`_Sound` |
| Echo | `echo-types` (Agda) @ `2bbdb49` | header re-characterised to the accurate definition — a **tropically-graded modality of structured information loss** (grade = min-plus = `Tropical.TropCost`), exact-on-a-fiber recoverability, variance (monad/comonad/adjunction) **deferred to upstream `--safe` Agda** (cf RETRACTION R-2026-05-18 + experimental R0–R4); added `EchoR` + `echoToResidue` (~ `EchoResidue.agda`) |
| L12 Epistemic | `epistemic-types` (Agda) @ `87ff8b4` | cross-doc + IS-NOT note (read-consistency is a *different* problem from canonical standpoint-indexed modality); **additive** `syncGrade` reusing sibling `Tropical.TropCost` (∞ = never-synced) — extant A10–A14 proofs untouched |

The min-plus grade is the **same object** across all three axes
(`echo-types` loss grade ≡ `Resource.Instances.MinPlus` ≡ `epistemic-types`
`EchoBridge.Grade` ≡ `Tropical.TropCost`) — echo/tropical/epistemic are one
graded structure.

**Upstream drafts prepped (local, unpushed, await owner review)** — three
extend-upstream candidates, each verified by its own prover:

- `tropical-resource-typing/Resource/Closure.lean` — Kleene/Floyd-Warshall
  all-pairs closure functor over `[ResourceAlgebra R]` (order/monotonicity/bound
  half proved; star-equation algebra deferred). `lake build` green, no axioms.
- `epistemic-types/src/EpistemicTypes/ReadConsistency.agda` — version-monotone
  re-sync liveness as a concrete `AccessibleModality` instance. `--safe`, closed.
- `echo-types/proofs/agda/EchoDisplayed.agda` — `Displayed`/`DispHom`/
  `fromHomOver` fibration packaging (no comonad claims). `--safe`, closed.

Nothing pushed or PR'd — drafts are for owner review per the stop-first rule.
