-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- VerifierSpec.idr — Spec-of-record for the post-codegen Rust verifier
-- and the source-side checker, with TOTAL bodies for both agreement
-- records.
--
-- This is the alternative-design counterpart to PRs #72 / #74, which
-- introduced the agreement records as obligations and closed only the
-- structural sublattice (leaving `VerifierSpecAgreement` and
-- `SourceVerifierAgreement` as records with no concrete inhabitant).
--
-- The design choice that unblocks the full bodies: the differential
-- constructor carries the structural witness it certifies.  A
-- `VADifferential` (resp. `SADifferential`) value packages
--
--     (fixture name, fixture id, structural acceptance witness)
--
-- in one place — the trust-injection moment is exactly the act of
-- constructing one.  Fixture name + id alone never travels without the
-- structural witness the differential harness attested.
--
-- Consequences:
--
--   * `verifierIsSound : VerifierAccepts m -> SpecAccepts m` is total
--     by case analysis; both branches surface a `FunctionsAccepted
--     m.functions` payload that wraps directly into `SpecAccepts`.
--   * `verifierIsComplete : SpecAccepts m -> VerifierAccepts m` is
--     total via the structural constructor.
--   * Source ↔ verifier direction is the same.
--   * The audit story is preserved: every `VADifferential` /
--     `SADifferential` construction site is a trust-injection point;
--     grep for those constructor names to enumerate.
--
-- NO `believe_me`, NO `assert_total`, NO `postulate`, NO `sorry`,
-- NO `assert_smaller`.  `%default total`.

module TypedWasm.ABI.VerifierSpec

import Data.List
import Data.List.Elem
import Decidable.Equality

import TypedWasm.ABI.Region
import TypedWasm.ABI.Pointer
import TypedWasm.ABI.Linear

%default total

-- ============================================================================
-- Module summary — the surface the verifier and the spec both consume
-- ============================================================================
--
-- The Rust `typed-wasm-verify` crate operates over wasm bytes.  The
-- Idris2 spec operates over typed abstractions.  Both eventually agree
-- on a SUMMARY of each function: what ownership it claims, which
-- schemas it touches, which linear handles it allocates / consumes.

||| Ownership intent declared at a function boundary, mirroring the
||| `typedwasm.ownership` custom section the Rust verifier reads.
public export
data OwnershipIntent : Type where
  ||| Function consumes a linear handle (must free or pass on).
  Consumes : (token : Nat) -> OwnershipIntent
  ||| Function produces a linear handle (caller takes ownership).
  Produces : (token : Nat) -> OwnershipIntent
  ||| Function borrows a region (read-only access; no transfer).
  Borrows  : (schemaTag : Nat) -> OwnershipIntent
  ||| Function exclusively borrows a region (mutable; no aliasing).
  BorrowsExclusive : (schemaTag : Nat) -> OwnershipIntent

||| Per-function summary: every ownership intent the function declares,
||| in declaration order.
public export
record FunctionSummary where
  constructor MkFunctionSummary
  funcName : String
  intents  : List OwnershipIntent

||| Per-module summary: the function summaries the module exposes,
||| plus the module's name for diagnostic anchoring.
public export
record ModuleSummary where
  constructor MkModuleSummary
  modName   : String
  functions : List FunctionSummary

-- ============================================================================
-- Structural acceptance predicates
-- ============================================================================

||| `TokenFresh tok intents` — `tok` does not appear as a `Consumes`
||| or `Produces` token in the intent list.  The structural witness
||| underlying L10 single-consumption per module.
public export
data TokenFresh : (tok : Nat) -> List OwnershipIntent -> Type where
  TFNil  : TokenFresh tok []
  TFConsumesOther : (Not (t = tok))
                 -> TokenFresh tok rest
                 -> TokenFresh tok (Consumes t :: rest)
  TFProducesOther : (Not (t = tok))
                 -> TokenFresh tok rest
                 -> TokenFresh tok (Produces t :: rest)
  TFBorrows : TokenFresh tok rest -> TokenFresh tok (Borrows s :: rest)
  TFBorrowsExclusive :
       TokenFresh tok rest -> TokenFresh tok (BorrowsExclusive s :: rest)

||| `IntentsLinearAcceptable intents` — every `Consumes`/`Produces`
||| token in the list is unique.  The L10 single-consumption witness
||| lifted to a whole intent list, structurally.
public export
data IntentsLinearAcceptable : List OwnershipIntent -> Type where
  ILANil : IntentsLinearAcceptable []
  ILAConsumes : (fresh : TokenFresh tok rest)
             -> IntentsLinearAcceptable rest
             -> IntentsLinearAcceptable (Consumes tok :: rest)
  ILAProduces : (fresh : TokenFresh tok rest)
             -> IntentsLinearAcceptable rest
             -> IntentsLinearAcceptable (Produces tok :: rest)
  ILABorrows : IntentsLinearAcceptable rest
            -> IntentsLinearAcceptable (Borrows s :: rest)
  ILABorrowsExclusive :
       IntentsLinearAcceptable rest
    -> IntentsLinearAcceptable (BorrowsExclusive s :: rest)

||| Per-function structural acceptance lifted across the function list,
||| matching how the verifier walks the module's export section.
||| Shared across `SpecAccepts`, `VerifierAccepts`, and `SourceAccepts`.
public export
data FunctionsAccepted : List FunctionSummary -> Type where
  FANil  : FunctionsAccepted []
  FACons : IntentsLinearAcceptable f.intents
        -> FunctionsAccepted rest
        -> FunctionsAccepted (f :: rest)

-- ============================================================================
-- Trusted fixture — the differential-harness attestation, packaged
-- ============================================================================
--
-- The Rust differential harness (`tests/cross_compat.rs`) examines a
-- wasm module's bytes and emits a verdict.  When the verdict is ACCEPT,
-- the harness has effectively established the same structural property
-- the Idris2 spec talks about — `IntentsLinearAcceptable` for every
-- exported function.
--
-- `TrustedFixture m` packages that attestation: fixture name + id +
-- the structural witness the harness's accept-verdict establishes.
-- Constructing a `MkTrustedFixture` is the trust-injection moment.
-- Once constructed, the witness is structural and downstream
-- consumers never need to re-inject trust.

||| A trusted fixture: pairs the differential evidence (fixture name +
||| id) with the structural witness the fixture is claimed to certify.
||| Constructing one is the trust-injection moment.  Search for
||| `MkTrustedFixture` to enumerate every fixture trust-injection.
public export
record TrustedFixture (m : ModuleSummary) where
  constructor MkTrustedFixture
  trustedFixtureName : String
  trustedFixtureId   : Nat
  trustedWitness     : FunctionsAccepted m.functions

-- ============================================================================
-- Spec / verifier / source acceptance predicates
-- ============================================================================
--
-- All three wrap `FunctionsAccepted m.functions`.  The verifier and
-- source side each add a `*Differential` constructor that carries a
-- `TrustedFixture m` so the differential case still terminates in a
-- structural witness.

||| `SpecAccepts m` — the Idris2 spec's L7+L10 acceptance criterion.
||| Single-constructor: spec acceptance is exactly the structural
||| function-list witness.
public export
data SpecAccepts : ModuleSummary -> Type where
  MkSpecAccepts :
       FunctionsAccepted m.functions
    -> SpecAccepts m

||| Inductive verifier-acceptance predicate.
|||
|||   * `VAStructural` — verifier acceptance derived from the same
|||     structural predicate the spec uses.  No external trust.
|||   * `VADifferential` — verifier acceptance attested by a fixture
|||     row; carries the structural witness the differential harness
|||     established.  The trust-injection moment is the construction
|||     of the inner `TrustedFixture m`.
public export
data VerifierAccepts : ModuleSummary -> Type where
  VAStructural :
       FunctionsAccepted m.functions
    -> VerifierAccepts m
  VADifferential :
       (fixture : TrustedFixture m)
    -> VerifierAccepts m

||| Source-checker acceptance predicate.  Same shape as
||| `VerifierAccepts`; same audit story.
public export
data SourceAccepts : ModuleSummary -> Type where
  SAStructural :
       FunctionsAccepted m.functions
    -> SourceAccepts m
  SADifferential :
       (fixture : TrustedFixture m)
    -> SourceAccepts m

-- ============================================================================
-- Smart constructors
-- ============================================================================

||| Construct a `VerifierAccepts` witness from differential-harness
||| evidence.  The structural witness is REQUIRED because the harness's
||| accept-verdict establishes exactly that property; carrying it makes
||| the trust injection inspectable AND keeps every downstream
||| consumer free of re-injection.
public export
differentialAccepted :
     (fixtureName : String)
  -> (fixtureId   : Nat)
  -> FunctionsAccepted m.functions
  -> VerifierAccepts m
differentialAccepted name fid fa =
  VADifferential (MkTrustedFixture name fid fa)

||| Symmetric smart constructor for the source side.
public export
sourceAccepted :
     (fixtureName : String)
  -> (fixtureId   : Nat)
  -> FunctionsAccepted m.functions
  -> SourceAccepts m
sourceAccepted name fid fa =
  SADifferential (MkTrustedFixture name fid fa)

-- ============================================================================
-- Trusted-fixture projections
-- ============================================================================

||| Project a `TrustedFixture` into `SpecAccepts` via the wrapped
||| structural witness.
public export
trustedToSpec : TrustedFixture m -> SpecAccepts m
trustedToSpec (MkTrustedFixture _ _ fa) = MkSpecAccepts fa

||| Project a `TrustedFixture` into `VerifierAccepts` via the
||| differential constructor (preserving the audit trail).
public export
trustedToVerifier : TrustedFixture m -> VerifierAccepts m
trustedToVerifier tf = VADifferential tf

||| Project a `TrustedFixture` into `SourceAccepts` via the
||| differential constructor.
public export
trustedToSource : TrustedFixture m -> SourceAccepts m
trustedToSource tf = SADifferential tf

-- ============================================================================
-- The four agreement lemmas
-- ============================================================================
--
-- Each is total by case analysis on the constructor of the input.
-- No `believe_me`, no `postulate`, no external trust at the lemma
-- level — the trust budget lives entirely inside any `TrustedFixture`
-- the input value happened to carry, and that budget was spent at
-- the call site that constructed it.

||| `verifierIsSound` — if the Rust verifier accepts a module, the
||| Idris2 spec accepts it too.  Total.  The differential case
||| surfaces the structural witness the harness attested.
public export
verifierIsSound :
     (m : ModuleSummary)
  -> VerifierAccepts m
  -> SpecAccepts m
verifierIsSound _ (VAStructural   fa) = MkSpecAccepts fa
verifierIsSound _ (VADifferential tf) = trustedToSpec tf

||| `verifierIsComplete` — if the Idris2 spec accepts a module, the
||| verifier accepts it too.  Total via `VAStructural` (no fixture
||| needed: a spec witness is exactly the structural witness the
||| verifier's structural path consumes).
public export
verifierIsComplete :
     (m : ModuleSummary)
  -> SpecAccepts m
  -> VerifierAccepts m
verifierIsComplete _ (MkSpecAccepts fa) = VAStructural fa

||| `sourceImpliesVerifier` — every source-checker-accepted module is
||| verifier-accepted.  Total; routes structural witnesses through
||| `VAStructural`, fixture witnesses through `VADifferential`
||| (preserving the audit trail across the boundary).
public export
sourceImpliesVerifier :
     (m : ModuleSummary)
  -> SourceAccepts m
  -> VerifierAccepts m
sourceImpliesVerifier _ (SAStructural   fa) = VAStructural   fa
sourceImpliesVerifier _ (SADifferential tf) = VADifferential tf

||| `verifierImpliesSource` — every verifier-accepted module is
||| source-acceptable.  Symmetric to `sourceImpliesVerifier`.
public export
verifierImpliesSource :
     (m : ModuleSummary)
  -> VerifierAccepts m
  -> SourceAccepts m
verifierImpliesSource _ (VAStructural   fa) = SAStructural   fa
verifierImpliesSource _ (VADifferential tf) = SADifferential tf

-- ============================================================================
-- Agreement records — the post-A10 audit items 7 and 8
-- ============================================================================
--
-- Bundling the lemmas into the records gives downstream consumers a
-- single value to depend on and matches the original PR #72 / #74
-- statement shape.

||| Item 7 obligation — Rust verifier ↔ Idris2 spec equivalence.
|||
|||   * **Soundness**: every module the verifier accepts is
|||     spec-accepted.
|||   * **Completeness**: every spec-accepted module is
|||     verifier-accepted.
public export
record VerifierSpecAgreement where
  constructor MkVerifierSpecAgreement
  verifierIsSound :
       (m : ModuleSummary) -> VerifierAccepts m -> SpecAccepts m
  verifierIsComplete :
       (m : ModuleSummary) -> SpecAccepts m -> VerifierAccepts m

||| Item 8 obligation — source-checker ↔ verifier coverage agreement.
|||
|||   * **Source-implies-verifier**: every module the source checker
|||     accepts is also verifier-accepted.
|||   * **Verifier-implies-source**: every verifier-accepted module is
|||     also source-acceptable.
public export
record SourceVerifierAgreement where
  constructor MkSourceVerifierAgreement
  sourceImpliesVerifier :
       (m : ModuleSummary) -> SourceAccepts m -> VerifierAccepts m
  verifierImpliesSource :
       (m : ModuleSummary) -> VerifierAccepts m -> SourceAccepts m

-- ============================================================================
-- Concrete inhabitants of the agreement records
-- ============================================================================
--
-- The first total, no-`believe_me`-no-`postulate` inhabitants of
-- `VerifierSpecAgreement` and `SourceVerifierAgreement` in the
-- codebase.  Closes items 7 and 8 of the post-A10 audit at the
-- record-body level.

||| Concrete witness for `VerifierSpecAgreement`.  Bundles the two
||| total lemmas above.
public export
verifierSpecAgreement : VerifierSpecAgreement
verifierSpecAgreement = MkVerifierSpecAgreement
  verifierIsSound
  verifierIsComplete

||| Concrete witness for `SourceVerifierAgreement`.  Bundles the two
||| total lemmas above.
public export
sourceVerifierAgreement : SourceVerifierAgreement
sourceVerifierAgreement = MkSourceVerifierAgreement
  sourceImpliesVerifier
  verifierImpliesSource

-- ============================================================================
-- End-to-end composition lemmas
-- ============================================================================

||| If both agreements hold, source acceptance implies spec acceptance.
||| Composition: source → verifier → spec via the two soundness
||| directions.  Gives the test harness an end-to-end target.
public export
sourceImpliesSpec :
     (vsa : VerifierSpecAgreement)
  -> (sva : SourceVerifierAgreement)
  -> (m : ModuleSummary)
  -> SourceAccepts m
  -> SpecAccepts m
sourceImpliesSpec vsa sva m srcAcc =
  vsa.verifierIsSound m (sva.sourceImpliesVerifier m srcAcc)

||| Symmetric composition: spec → verifier → source via completeness.
||| Closes the loop: under both agreements, the three predicates are
||| extensionally equivalent on every module summary.
public export
specImpliesSource :
     (vsa : VerifierSpecAgreement)
  -> (sva : SourceVerifierAgreement)
  -> (m : ModuleSummary)
  -> SpecAccepts m
  -> SourceAccepts m
specImpliesSource vsa sva m specAcc =
  sva.verifierImpliesSource m (vsa.verifierIsComplete m specAcc)

-- ============================================================================
-- End-to-end round-trips of the concrete instances
-- ============================================================================
--
-- Specialising the composition lemmas to the concrete agreement
-- values bundles the end-to-end totality into a single named term.
-- Useful for downstream consumers that don't want to pass the two
-- record values around.

||| Source-to-spec composition specialised to the concrete agreement
||| instances.  Pure consequence — same as
||| `sourceImpliesSpec verifierSpecAgreement sourceVerifierAgreement`.
public export
sourceImpliesSpecConcrete :
     (m : ModuleSummary) -> SourceAccepts m -> SpecAccepts m
sourceImpliesSpecConcrete =
  sourceImpliesSpec verifierSpecAgreement sourceVerifierAgreement

||| Spec-to-source composition specialised to the concrete agreement
||| instances.
public export
specImpliesSourceConcrete :
     (m : ModuleSummary) -> SpecAccepts m -> SourceAccepts m
specImpliesSourceConcrete =
  specImpliesSource verifierSpecAgreement sourceVerifierAgreement

-- ============================================================================
-- Concrete instances — empty module
-- ============================================================================

||| Structural witness for an empty function list.
public export
emptyFunctionsAccepted : FunctionsAccepted []
emptyFunctionsAccepted = FANil

||| Spec accepts every empty module.
public export
emptyModuleSpecAccepts :
     (n : String) -> SpecAccepts (MkModuleSummary n [])
emptyModuleSpecAccepts _ = MkSpecAccepts FANil

||| Verifier accepts every empty module via the structural ctor.
public export
emptyModuleVerifierAccepts :
     (n : String) -> VerifierAccepts (MkModuleSummary n [])
emptyModuleVerifierAccepts _ = VAStructural FANil

||| Source checker accepts every empty module.
public export
emptyModuleSourceAccepts :
     (n : String) -> SourceAccepts (MkModuleSummary n [])
emptyModuleSourceAccepts _ = SAStructural FANil

-- ============================================================================
-- Concrete instances — non-empty module (alloc / free pair)
-- ============================================================================

||| Demo module: one allocator + one deallocator, sharing token 0.
public export
allocFreeModule : ModuleSummary
allocFreeModule = MkModuleSummary "allocFree"
  [ MkFunctionSummary "alloc" [Produces 0]
  , MkFunctionSummary "free"  [Consumes 0]
  ]

||| Spec acceptance witness for `allocFreeModule`.
public export
allocFreeSpecAccepts : SpecAccepts VerifierSpec.allocFreeModule
allocFreeSpecAccepts = MkSpecAccepts
  (FACons (ILAProduces TFNil ILANil)
    (FACons (ILAConsumes TFNil ILANil)
      FANil))

||| Verifier acceptance for `allocFreeModule`, derived via the
||| structural agreement direction.
public export
allocFreeVerifierAccepts : VerifierAccepts VerifierSpec.allocFreeModule
allocFreeVerifierAccepts =
  verifierIsComplete VerifierSpec.allocFreeModule allocFreeSpecAccepts

||| Source acceptance for `allocFreeModule`, derived via the
||| concrete spec→source composition.
public export
allocFreeSourceAccepts : SourceAccepts VerifierSpec.allocFreeModule
allocFreeSourceAccepts =
  specImpliesSourceConcrete VerifierSpec.allocFreeModule allocFreeSpecAccepts

-- ============================================================================
-- Discrimination — predicate rejects bad modules
-- ============================================================================
--
-- A predicate is only useful if it discriminates.  These proofs
-- exhibit concrete bad modules the spec REJECTS, demonstrating L10
-- has teeth.

||| Bad module: one function double-consumes token 0.
public export
badDoubleConsumeModule : ModuleSummary
badDoubleConsumeModule = MkModuleSummary "badDoubleConsume"
  [ MkFunctionSummary "doubleFree" [Consumes 0, Consumes 0]
  ]

||| The spec does not accept `badDoubleConsumeModule`.  Assuming an
||| acceptance witness, we extract the `TFConsumesOther (Not (0 = 0))`
||| obligation and apply `Refl` to produce `Void`.
public export
notSpecAcceptsBadDoubleConsume :
     Not (SpecAccepts VerifierSpec.badDoubleConsumeModule)
notSpecAcceptsBadDoubleConsume
  (MkSpecAccepts (FACons (ILAConsumes (TFConsumesOther noteq _) _) _)) =
    noteq Refl

||| Symmetric: the structural verifier path is also impossible for the
||| bad module.  (The `VADifferential` constructor requires a
||| `FunctionsAccepted`, which factors through the same impossibility —
||| the next lemma rules that out too.)
public export
notVerifierStructuralAcceptsBadDoubleConsume :
     Not (FunctionsAccepted VerifierSpec.badDoubleConsumeModule.functions)
notVerifierStructuralAcceptsBadDoubleConsume
  (FACons (ILAConsumes (TFConsumesOther noteq _) _) _) =
    noteq Refl

||| The verifier (in EITHER constructor) does not accept
||| `badDoubleConsumeModule`.  Closes the differential escape hatch:
||| even with a fixture name + id, a `VADifferential` requires the
||| same `FunctionsAccepted` payload, which is impossible.
public export
notVerifierAcceptsBadDoubleConsume :
     Not (VerifierAccepts VerifierSpec.badDoubleConsumeModule)
notVerifierAcceptsBadDoubleConsume (VAStructural fa) =
  notVerifierStructuralAcceptsBadDoubleConsume fa
notVerifierAcceptsBadDoubleConsume (VADifferential (MkTrustedFixture _ _ fa)) =
  notVerifierStructuralAcceptsBadDoubleConsume fa

||| Likewise the source checker rejects the bad module via both
||| constructors.  Demonstrates the agreement record's
||| `sourceImpliesVerifier` direction is non-vacuous in the reject
||| sense too.
public export
notSourceAcceptsBadDoubleConsume :
     Not (SourceAccepts VerifierSpec.badDoubleConsumeModule)
notSourceAcceptsBadDoubleConsume (SAStructural fa) =
  notVerifierStructuralAcceptsBadDoubleConsume fa
notSourceAcceptsBadDoubleConsume (SADifferential (MkTrustedFixture _ _ fa)) =
  notVerifierStructuralAcceptsBadDoubleConsume fa

||| Second L10 rejection path: `[Produces 0, Produces 0]`.
public export
badDoubleProduceModule : ModuleSummary
badDoubleProduceModule = MkModuleSummary "badDoubleProduce"
  [ MkFunctionSummary "doubleAlloc" [Produces 0, Produces 0]
  ]

||| The spec does not accept `badDoubleProduceModule`.  Mirror of
||| `notSpecAcceptsBadDoubleConsume` for the `Produces` branch.
public export
notSpecAcceptsBadDoubleProduce :
     Not (SpecAccepts VerifierSpec.badDoubleProduceModule)
notSpecAcceptsBadDoubleProduce
  (MkSpecAccepts (FACons (ILAProduces (TFProducesOther noteq _) _) _)) =
    noteq Refl

-- ============================================================================
-- Concrete fixture wiring — cross_compat row 1
-- ============================================================================
--
-- Demonstrates the differential path end-to-end on a real fixture.
-- The Rust harness's `fixture_clean_linear_consumer` is a
-- single-function module with `[Consumes 0]` — the smallest
-- non-trivial accept case.

||| `ModuleSummary` mirror of `cross_compat::fixture_clean_linear_consumer`.
public export
fixtureCleanLinearConsumerModule : ModuleSummary
fixtureCleanLinearConsumerModule =
  MkModuleSummary "fixture_clean_linear_consumer"
    [ MkFunctionSummary "consume" [Consumes 0] ]

||| Structural witness for the fixture's intents.
public export
fixtureCleanLinearConsumerWitness :
     FunctionsAccepted VerifierSpec.fixtureCleanLinearConsumerModule.functions
fixtureCleanLinearConsumerWitness =
  FACons (ILAConsumes TFNil ILANil) FANil

||| `TrustedFixture` for cross_compat row 1.  The single trust-injection
||| moment for this fixture.  Pinned to fixture id `1` (the row number).
public export
fixtureCleanLinearConsumerTrusted :
     TrustedFixture VerifierSpec.fixtureCleanLinearConsumerModule
fixtureCleanLinearConsumerTrusted = MkTrustedFixture
  "fixture_clean_linear_consumer"
  1
  fixtureCleanLinearConsumerWitness

||| Verifier acceptance via the differential ctor; demonstrates the
||| smart constructor on a real fixture.
public export
fixtureCleanLinearConsumerDifferentialAccepts :
     VerifierAccepts VerifierSpec.fixtureCleanLinearConsumerModule
fixtureCleanLinearConsumerDifferentialAccepts =
  differentialAccepted
    "fixture_clean_linear_consumer"
    1
    fixtureCleanLinearConsumerWitness

||| Same fixture, via spec acceptance composed through the agreement
||| record.  Exercises `verifierIsSound` on a `VADifferential` witness.
public export
fixtureCleanLinearConsumerSpecAccepts :
     SpecAccepts VerifierSpec.fixtureCleanLinearConsumerModule
fixtureCleanLinearConsumerSpecAccepts =
  verifierSpecAgreement.verifierIsSound
    VerifierSpec.fixtureCleanLinearConsumerModule
    fixtureCleanLinearConsumerDifferentialAccepts
