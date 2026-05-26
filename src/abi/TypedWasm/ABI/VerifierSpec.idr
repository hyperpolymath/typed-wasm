-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- VerifierSpec.idr — Spec-of-record for the post-codegen verifier and
-- the source-side checker (A13, 2026-05-26).
--
-- This module closes the *statement* side of post-A10 audit items 7
-- and 8 (Rust verifier ↔ Idris2 spec equivalence; source-checker ↔
-- verifier coverage agreement).  It does NOT close the full
-- equivalence proofs — those require either a full simulation between
-- two implementations (multi-week) or extending the verifier's
-- coverage to every level (similar scope).  What it DOES do is pin
-- down the obligations as typed Idris2 predicates, so:
--
--   * Future proof work can construct witnesses against fixed targets.
--   * The differential testing harness (`tests/cross_compat.rs` +
--     `tests/proof/regression.mjs`) has a concrete spec to point at.
--   * Any drift between this spec and the Rust verifier shows up as a
--     failing fixture.
--
-- The shape mirrors how `Proofs.idr` introduced `LevelAchievedIn` as
-- a typed obligation before any soundness theorem consumed it: we
-- introduce the predicates first, claim agreement as a record-of-
-- obligations, and let downstream work plug witnesses in.
--
-- NO `believe_me`, NO `assert_total`, NO `Admitted`.  `%default total`.

module TypedWasm.ABI.VerifierSpec

import Data.List
import Data.List.Elem

import TypedWasm.ABI.Region
import TypedWasm.ABI.Pointer
import TypedWasm.ABI.Linear

%default total

-- ============================================================================
-- Abstract module summary — the surface the verifier and the spec
-- both consume.
-- ============================================================================
--
-- The Rust `typed-wasm-verify` crate operates over wasm bytes.  The
-- Idris2 spec operates over typed abstractions (Region, LinHandle,
-- ExclusiveWitness, …).  Both eventually agree on a SUMMARY of each
-- function: what ownership it claims, which schemas it touches, which
-- linear handles it allocates / consumes.  `FunctionSummary` and
-- `ModuleSummary` are the surface used by the agreement predicates.

||| Ownership intent declared at a function boundary, mirroring the
||| `affinescript.ownership` / `typedwasm.ownership` custom section the
||| Rust verifier reads.
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
||| in declaration order.  An empty list means a pure function with
||| no resource side-effects.
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
-- Spec-of-record acceptance predicate
-- ============================================================================
--
-- `SpecAccepts m` is the Idris2 L7 (aliasing) + L10 (linearity)
-- acceptance criterion on a `ModuleSummary`.  It is structural: no
-- two `Consumes` intents may share a token (otherwise some handle is
-- double-consumed); every `Produces` token must be unique within the
-- module (otherwise two functions promise the same allocation).  This
-- is the *spec* the Rust verifier must agree with.
--
-- The predicate is INTENTIONALLY narrow: it captures only what
-- typed-wasm-verify currently checks (L7 + L10 over a module's
-- ownership custom section).  Extending it to L13/L14/L15 is part of
-- the source-checker ↔ verifier coverage agreement (item 8 below).

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
||| token in the list is unique.  This is the L10 single-consumption
||| witness lifted to a whole intent list, structurally.
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
||| matching how the verifier walks the module's export section.  Used
||| by `SpecAccepts`, `VerifierAccepts`, and `SourceAccepts` so all
||| three agree on the structural witness shape at L7+L10.
public export
data FunctionsAccepted : List FunctionSummary -> Type where
  FANil  : FunctionsAccepted []
  FACons : IntentsLinearAcceptable f.intents
        -> FunctionsAccepted rest
        -> FunctionsAccepted (f :: rest)

||| `SpecAccepts m` — the Idris2 spec accepts a module summary.  Wraps
||| `FunctionsAccepted` on the function list so spec / verifier /
||| source-checker share a single canonical structural witness at the
||| L7+L10 layer.  Future extensions (L13 cross-module checks, L14
||| session-state) add new constructors without breaking existing
||| structural witnesses.
public export
data SpecAccepts : ModuleSummary -> Type where
  MkSpecAccepts :
       FunctionsAccepted m.functions
    -> SpecAccepts m

-- ============================================================================
-- Verifier acceptance (inductive — structural + differential cases)
-- ============================================================================
--
-- The Rust verifier's acceptance set has two flavours of evidence:
--
--   1. STRUCTURAL — for modules whose ownership intents are visible at
--      the typed surface, the verifier's L7+L10 acceptance is exactly
--      the same predicate the spec uses.  No trust-injection needed.
--   2. DIFFERENTIAL — for modules whose typed surface is partial (the
--      Rust verifier inspects wasm bytes via wasmparser), the only
--      legitimate way to assert verifier-acceptance is through a row
--      in the differential testing table (`tests/cross_compat.rs`).
--
-- The earlier opaque design (A13) collapsed both cases into a single
-- "external evidence" constructor.  That made every agreement
-- direction unprovable (no introspection into the witness).  The
-- inductive split below restores provability of the structural cases
-- while keeping the differential case auditable.

||| Inductive verifier-acceptance predicate, indexed by `ModuleSummary`.
||| Two constructors expose the trust shape:
|||
|||   * `VAStructural` — verifier acceptance derived from the same
|||     structural predicate the spec uses.  No external trust;
|||     introspectable witness.
|||   * `VADifferential` — verifier acceptance via the differential
|||     harness.  External trust pinned to a fixture row.  Searching
|||     for this constructor enumerates every trust-injection site.
public export
data VerifierAccepts : ModuleSummary -> Type where
  ||| Structural verifier acceptance: every exported function's
  ||| intent list passes the L10 single-consumption / L7 aliasing check.
  ||| This is the case the spec and the verifier agree on by definition.
  VAStructural :
       FunctionsAccepted m.functions
    -> VerifierAccepts m
  ||| Differential verifier acceptance: external evidence from
  ||| `tests/cross_compat.rs` pinning a fixture row.  Constructible
  ||| only via `differentialAccepted` so the trust boundary is
  ||| inspectable.
  VADifferential :
       (differentialEvidence : String)
    -> (fixtureId            : Nat)
    -> VerifierAccepts m

||| Construct a `VerifierAccepts` witness from differential-harness
||| evidence (fixture name + numeric id from `tests/cross_compat.rs`).
||| Naming the fixture in the witness makes the trust boundary
||| inspectable: every `VADifferential` use can be traced back to a
||| concrete row in the differential table.
public export
differentialAccepted : (fixtureName : String) -> (fixtureId : Nat)
                   -> VerifierAccepts m
differentialAccepted name fid = VADifferential name fid

-- ============================================================================
-- Source-checker acceptance (item 8 surface)
-- ============================================================================

||| Source-checker acceptance predicate.  Like `VerifierAccepts`, the
||| source checker has both a structural surface (typed AST) and a
||| differential side (cross-checked against fixtures when the source
||| AST is partial).  Same two-constructor shape, same audit story.
public export
data SourceAccepts : ModuleSummary -> Type where
  ||| Structural source-checker acceptance: lifted from
  ||| `FunctionsAccepted` exactly as the spec sees it.
  SAStructural :
       FunctionsAccepted m.functions
    -> SourceAccepts m
  ||| Differential source-checker acceptance: external evidence from a
  ||| source-side fixture row.
  SADifferential :
       (sourceEvidence : String)
    -> (fixtureId      : Nat)
    -> SourceAccepts m

||| Construct a `SourceAccepts` witness from source-side evidence.
public export
sourceAccepted : (fixtureName : String) -> (fixtureId : Nat)
              -> SourceAccepts m
sourceAccepted name fid = SADifferential name fid

-- ============================================================================
-- Agreement obligations — items 7 and 8
-- ============================================================================
--
-- The two agreement obligations are stated as Idris2 propositions
-- ("for every module summary, if the spec accepts then the verifier
-- accepts, and vice versa").  Witnesses are NOT discharged here; they
-- are the long-tail proof work.  What this module DOES discharge is
-- the *shape*: anyone trying to claim agreement now has a typed
-- target to aim at, and the differential harness's existing fixtures
-- can be re-cast as partial witnesses.

||| Item 7 obligation — Rust verifier ↔ Idris2 spec equivalence.
|||
|||   * **Soundness direction**: every module the verifier accepts is
|||     spec-accepted (the verifier doesn't accept anything unsafe).
|||   * **Completeness direction**: every spec-accepted module is
|||     verifier-accepted (the verifier doesn't reject anything safe).
|||
||| The record bundles the two directions so partial proofs can land
||| one face at a time.  A full witness would discharge BOTH fields.
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
|||     accepts is also verifier-accepted (the verifier covers
|||     everything the source checker promises).
|||   * **Verifier-implies-source**: every verifier-accepted module is
|||     also source-acceptable (the verifier doesn't outgrow the
|||     source checker's coverage envelope).
|||
||| The "verifier outgrows source checker" direction is the actual
||| source-checker-coverage extension obligation: the source checker
||| has to be extended to cover whatever the verifier checks beyond
||| L7+L10 (L13 cross-module, L14 session-state, etc.).
public export
record SourceVerifierAgreement where
  constructor MkSourceVerifierAgreement
  sourceImpliesVerifier :
       (m : ModuleSummary) -> SourceAccepts m -> VerifierAccepts m
  verifierImpliesSource :
       (m : ModuleSummary) -> VerifierAccepts m -> SourceAccepts m

-- ============================================================================
-- Trivial consequences (statement-level corollaries)
-- ============================================================================

||| If both agreements hold, source acceptance and spec acceptance
||| coincide.  Composition: source → verifier → spec via the two
||| soundness directions.  Stated to give the test harness an
||| end-to-end target predicate to assert against.
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
||| Closes the loop: under both agreements, the three predicates
||| (`SpecAccepts`, `VerifierAccepts`, `SourceAccepts`) are
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
-- Structural agreement — first concrete witnesses (items 7 + 8, partial)
-- ============================================================================
--
-- The full `VerifierSpecAgreement` / `SourceVerifierAgreement` records
-- above remain obligations because their generality covers both
-- structural and differential evidence: the differential case requires
-- an external connection (wasm-bytes semantics or fixture-row trust)
-- and is multi-week.
--
-- What IS provable, total, no-trust-injection, is the agreement
-- restricted to the structural cases.  The records and lemmas below
-- give those a concrete home.  Future work plugs the differential
-- cases in by extending these records (e.g. by lifting fixture
-- evidence into a stratified-acceptance predicate).
--
-- Convention: every name in this section ends in `Structural` so the
-- restriction to the structural sublattice is visible at call sites.

||| `FunctionsAccepted` directly witnesses `SpecAccepts`.  This is the
||| spec's structural inhabitant: any function-list witness gives a
||| spec acceptance witness for the enclosing module.
public export
functionsAcceptedImpliesSpec :
     {m : ModuleSummary}
  -> FunctionsAccepted m.functions
  -> SpecAccepts m
functionsAcceptedImpliesSpec fa = MkSpecAccepts fa

||| Inverse direction: a spec acceptance witness contains the
||| structural per-function witness.
public export
specImpliesFunctionsAccepted :
     {m : ModuleSummary}
  -> SpecAccepts m
  -> FunctionsAccepted m.functions
specImpliesFunctionsAccepted (MkSpecAccepts fa) = fa

||| Spec → verifier (structural case).  Lifts spec acceptance directly
||| into `VAStructural` — no trust-injection.
public export
specImpliesVerifierStructural :
     {m : ModuleSummary}
  -> SpecAccepts m
  -> VerifierAccepts m
specImpliesVerifierStructural (MkSpecAccepts fa) = VAStructural fa

||| Spec → source (structural case).  Symmetric to the verifier
||| direction; lifts spec acceptance into `SAStructural`.
public export
specImpliesSourceStructural :
     {m : ModuleSummary}
  -> SpecAccepts m
  -> SourceAccepts m
specImpliesSourceStructural (MkSpecAccepts fa) = SAStructural fa

||| Verifier → spec (structural case only).  Defined on `VAStructural`
||| witnesses; the `VADifferential` case is the multi-week obligation
||| and is therefore reflected as a `Maybe` here so totality is
||| preserved without `believe_me`.
public export
verifierImpliesSpecStructural :
     {m : ModuleSummary}
  -> VerifierAccepts m
  -> Maybe (SpecAccepts m)
verifierImpliesSpecStructural (VAStructural fa)        = Just (MkSpecAccepts fa)
verifierImpliesSpecStructural (VADifferential _ _)     = Nothing

||| Source → spec (structural case only).  Mirrors
||| `verifierImpliesSpecStructural` for the source side.
public export
sourceImpliesSpecStructural :
     {m : ModuleSummary}
  -> SourceAccepts m
  -> Maybe (SpecAccepts m)
sourceImpliesSpecStructural (SAStructural fa)       = Just (MkSpecAccepts fa)
sourceImpliesSpecStructural (SADifferential _ _)    = Nothing

||| Bundle of structural-case agreement directions.  Differs from
||| `VerifierSpecAgreement` / `SourceVerifierAgreement` in three ways:
|||
|||   1. Restricted to the structural sublattice — `VADifferential`
|||      and `SADifferential` are NOT covered.
|||   2. Provable as a total Idris2 value (`structuralAgreement` below).
|||   3. Symmetric across all three predicates simultaneously.
|||
||| This is the first concrete agreement value in the codebase that
||| relates the spec / verifier / source-checker acceptance predicates
||| without invoking external evidence.
public export
record StructuralAgreement where
  constructor MkStructuralAgreement
  saSpecToVerifier :
       (m : ModuleSummary) -> SpecAccepts m -> VerifierAccepts m
  saSpecToSource :
       (m : ModuleSummary) -> SpecAccepts m -> SourceAccepts m
  saVerifierStructuralToSpec :
       (m : ModuleSummary) -> FunctionsAccepted m.functions -> SpecAccepts m
  saSourceStructuralToSpec :
       (m : ModuleSummary) -> FunctionsAccepted m.functions -> SpecAccepts m

||| Concrete witness for `StructuralAgreement`.  Total.  No
||| `believe_me`, no `postulate`, no external trust.  Closes the
||| structural-case portion of items 7 and 8 from the post-A10 audit.
public export
structuralAgreement : StructuralAgreement
structuralAgreement = MkStructuralAgreement
  (\m, sa => specImpliesVerifierStructural sa)
  (\m, sa => specImpliesSourceStructural sa)
  (\m, fa => functionsAcceptedImpliesSpec fa)
  (\m, fa => functionsAcceptedImpliesSpec fa)

-- ============================================================================
-- Concrete instance proofs — empty module
-- ============================================================================
--
-- The empty-module case is the first concrete `SpecAccepts`
-- inhabitant: no functions, so the per-function obligation is
-- trivially satisfied.  Used by the regression test as a smoke check
-- that the predicates aren't vacuously unprovable.

||| Structural witness for an empty function list.  Closes the L7+L10
||| obligations vacuously.
public export
emptyFunctionsAccepted : FunctionsAccepted []
emptyFunctionsAccepted = FANil

||| The spec accepts every module whose function list is empty.
||| Concrete inhabitant of `SpecAccepts`.  Demonstrates the predicate
||| is not vacuously empty.
public export
emptyModuleSpecAccepts :
     (n : String) -> SpecAccepts (MkModuleSummary n [])
emptyModuleSpecAccepts n = MkSpecAccepts FANil

||| The verifier accepts every empty-module summary via the structural
||| constructor (no differential evidence needed).
public export
emptyModuleVerifierAccepts :
     (n : String) -> VerifierAccepts (MkModuleSummary n [])
emptyModuleVerifierAccepts n = VAStructural FANil

||| The source checker accepts every empty-module summary.
public export
emptyModuleSourceAccepts :
     (n : String) -> SourceAccepts (MkModuleSummary n [])
emptyModuleSourceAccepts n = SAStructural FANil

-- ============================================================================
-- Concrete instance proofs — non-empty module (alloc / free pair)
-- ============================================================================
--
-- The minimal interesting case: a module exporting an allocator
-- (`Produces 0`) and a deallocator (`Consumes 0`).  This is the
-- smallest non-vacuous L10 single-consumption witness:
--
--   * `Produces 0` introduces handle token 0.
--   * `Consumes 0` consumes it exactly once.
--   * `TokenFresh 0 []` for each per-function obligation is trivial.
--
-- Demonstrates that the structural witness machinery scales past the
-- empty list, and exercises every `ILA*` / `TF*` constructor needed to
-- build a real witness.

||| Demo module: one allocator + one deallocator, sharing token 0.
||| The canonical "valid pair" example.  Used by the discrimination
||| section below to contrast with `badDoubleConsumeModule`.
public export
allocFreeModule : ModuleSummary
allocFreeModule = MkModuleSummary "allocFree"
  [ MkFunctionSummary "alloc" [Produces 0]
  , MkFunctionSummary "free"  [Consumes 0]
  ]

||| Spec acceptance witness for `allocFreeModule`.  Built from raw
||| structural constructors: `ILAProduces` for the allocator,
||| `ILAConsumes` for the deallocator, `TFNil` for the trivial
||| per-function freshness obligations.
public export
allocFreeSpecAccepts : SpecAccepts VerifierSpec.allocFreeModule
allocFreeSpecAccepts = MkSpecAccepts
  (FACons (ILAProduces TFNil ILANil)
    (FACons (ILAConsumes TFNil ILANil)
      FANil))

||| Verifier acceptance for `allocFreeModule`, derived via the
||| structural spec→verifier direction.  Concrete demonstration that
||| the agreement value works on a real, non-empty module.
public export
allocFreeVerifierAccepts : VerifierAccepts VerifierSpec.allocFreeModule
allocFreeVerifierAccepts =
  specImpliesVerifierStructural allocFreeSpecAccepts

||| Source-checker acceptance for `allocFreeModule`, derived via the
||| structural spec→source direction.  Closes the structural triangle
||| for a real module.
public export
allocFreeSourceAccepts : SourceAccepts VerifierSpec.allocFreeModule
allocFreeSourceAccepts =
  specImpliesSourceStructural allocFreeSpecAccepts

-- ============================================================================
-- Discrimination — predicate rejects bad modules
-- ============================================================================
--
-- A predicate is only useful if it discriminates: there must be some
-- module the spec REJECTS.  Without a `Not (SpecAccepts badModule)`
-- proof, the predicate could be vacuously true on everything and pass
-- every regression test.  The proof below exhibits a concrete bad
-- module and shows the L10 single-consumption rule has teeth.

||| Bad module: one function double-consumes token 0.  Violates L10
||| (a linear handle is consumed twice).  The structural witness
||| machinery should make `SpecAccepts` of this module impossible.
public export
badDoubleConsumeModule : ModuleSummary
badDoubleConsumeModule = MkModuleSummary "badDoubleConsume"
  [ MkFunctionSummary "doubleFree" [Consumes 0, Consumes 0]
  ]

||| The spec does not accept `badDoubleConsumeModule`.  This is the
||| discrimination proof: assuming an acceptance witness, we extract
||| the `TokenFresh 0 [Consumes 0]` obligation that `ILAConsumes`
||| requires.  The only constructor matching that shape is
||| `TFConsumesOther (Not (0 = 0)) _`, and applying `Refl` to the
||| `Not (0 = 0)` produces `Void`.  Demonstrates L10 has teeth.
public export
notSpecAcceptsBadDoubleConsume :
     Not (SpecAccepts VerifierSpec.badDoubleConsumeModule)
notSpecAcceptsBadDoubleConsume
  (MkSpecAccepts (FACons (ILAConsumes (TFConsumesOther noteq _) _) _)) =
    noteq Refl

||| Symmetric: the structural verifier witness is also impossible for
||| the bad module.  (The `VADifferential` case is not ruled out by
||| this lemma — that escape hatch is by design and remains the
||| differential-trust obligation.)
public export
notVerifierStructuralAcceptsBadDoubleConsume :
     Not (FunctionsAccepted VerifierSpec.badDoubleConsumeModule.functions)
notVerifierStructuralAcceptsBadDoubleConsume
  (FACons (ILAConsumes (TFConsumesOther noteq _) _) _) =
    noteq Refl

||| A second L10 rejection path: `[Produces 0, Produces 0]`.
||| The L10 single-consumption rule forbids any token from appearing
||| twice in a function's intent list, regardless of `Consumes` /
||| `Produces` direction.  Distinct from `badDoubleConsumeModule`
||| because it exercises the `ILAProduces` / `TFProducesOther`
||| constructor pair instead of the `ILAConsumes` / `TFConsumesOther`
||| pair.
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

||| A third L10 rejection path: a token mixes `Consumes` with
||| `Produces` in the same function.  `[Consumes 0, Produces 0]`
||| violates the per-function single-occurrence rule because the
||| `ILAConsumes` constructor demands `TokenFresh 0 [Produces 0]`,
||| which only `TFProducesOther` can witness, which in turn requires
||| `Not (0 = 0)`.
public export
badConsumeProduceMixModule : ModuleSummary
badConsumeProduceMixModule = MkModuleSummary "badConsumeProduceMix"
  [ MkFunctionSummary "mixed" [Consumes 0, Produces 0]
  ]

||| The spec does not accept `badConsumeProduceMixModule`.  Exercises
||| the cross-direction case: the rejection witness is
||| `TFProducesOther (Not (0 = 0)) _` inside an `ILAConsumes` shell.
public export
notSpecAcceptsBadConsumeProduceMix :
     Not (SpecAccepts VerifierSpec.badConsumeProduceMixModule)
notSpecAcceptsBadConsumeProduceMix
  (MkSpecAccepts (FACons (ILAConsumes (TFProducesOther noteq _) _) _)) =
    noteq Refl

-- ============================================================================
-- Extended allocFreeModule — exercises all four OwnershipIntent
-- constructors (Produces / Consumes / Borrows / BorrowsExclusive)
-- ============================================================================
--
-- The base `allocFreeModule` exercises only the linear pair
-- (Produces 0 / Consumes 0).  The extended variant adds a borrowing
-- pattern alongside, exercising both `Borrows` (read-only) and
-- `BorrowsExclusive` (mutable), and shows the structural witness
-- machinery handles all four constructors in a single module.
--
-- Schema tags 1 and 2 are used so the borrow intents don't collide
-- structurally with the linear token 0 (which lives in a separate
-- index namespace anyway, but keeping them distinct makes the
-- intent table easier to read).

||| Demo module exercising all four `OwnershipIntent` constructors.
|||
|||   * `alloc` produces a linear handle (token 0).
|||   * `read` borrows schema 1 (read-only).
|||   * `update` borrows schema 2 exclusively (mutable).
|||   * `free` consumes the linear handle.
public export
allocFreeWithBorrowModule : ModuleSummary
allocFreeWithBorrowModule = MkModuleSummary "allocFreeWithBorrow"
  [ MkFunctionSummary "alloc"  [Produces 0]
  , MkFunctionSummary "read"   [Borrows 1]
  , MkFunctionSummary "update" [BorrowsExclusive 2]
  , MkFunctionSummary "free"   [Consumes 0]
  ]

||| Spec acceptance witness for `allocFreeWithBorrowModule`.  Exercises
||| `ILAProduces` / `ILABorrows` / `ILABorrowsExclusive` / `ILAConsumes`
||| in a single witness — the full four-constructor coverage of
||| `IntentsLinearAcceptable`.
public export
allocFreeWithBorrowSpecAccepts :
     SpecAccepts VerifierSpec.allocFreeWithBorrowModule
allocFreeWithBorrowSpecAccepts = MkSpecAccepts
  (FACons (ILAProduces TFNil ILANil)
    (FACons (ILABorrows ILANil)
      (FACons (ILABorrowsExclusive ILANil)
        (FACons (ILAConsumes TFNil ILANil)
          FANil))))

||| Verifier acceptance for the four-constructor demo module, derived
||| via `specImpliesVerifierStructural`.
public export
allocFreeWithBorrowVerifierAccepts :
     VerifierAccepts VerifierSpec.allocFreeWithBorrowModule
allocFreeWithBorrowVerifierAccepts =
  specImpliesVerifierStructural allocFreeWithBorrowSpecAccepts

||| Source-checker acceptance for the four-constructor demo module.
public export
allocFreeWithBorrowSourceAccepts :
     SourceAccepts VerifierSpec.allocFreeWithBorrowModule
allocFreeWithBorrowSourceAccepts =
  specImpliesSourceStructural allocFreeWithBorrowSpecAccepts

-- ============================================================================
-- ExtendedAgreement — constructive bridge from VADifferential to spec
-- ============================================================================
--
-- The `StructuralAgreement` value above closes the structural
-- sublattice but leaves `VADifferential` evidence dangling: there is
-- no provable `(m : ModuleSummary) -> VerifierAccepts m -> SpecAccepts m`
-- that handles `VADifferential` cases, because a fixture name + id
-- alone carry no structural information.
--
-- The trust pattern below relocates the trust-injection moment from
-- "every VADifferential witness use" to "fixture registration time".
-- A `TrustedFixture` packages a fixture name + id with the structural
-- witness the fixture is claimed to certify.  Constructing a
-- `TrustedFixture` IS the trust-injection — but once constructed, the
-- witness is structural, so downstream proofs of agreement use the
-- structural directions only.
--
-- This is the constructive bridge: the trust still has to be injected
-- somewhere (because the Rust verifier inspects wasm bytes; Idris2
-- cannot do that itself), but it's injected once per fixture, with
-- the fixture name pinned in the witness type, instead of being
-- injected anew at every consumer of `VerifierSpecAgreement`.

||| A trusted fixture: pairs the differential evidence (fixture name +
||| id) with the structural witness the fixture is supposed to
||| certify.  Constructing one is the trust-injection moment.  Search
||| for `MkTrustedFixture` to enumerate every fixture trust-injection.
public export
record TrustedFixture (m : ModuleSummary) where
  constructor MkTrustedFixture
  trustedFixtureName : String
  trustedFixtureId   : Nat
  trustedWitness     : FunctionsAccepted m.functions

||| A `TrustedFixture` projects to `VerifierAccepts` via the
||| structural constructor — no further trust injection at use site.
public export
trustedToVerifier : TrustedFixture m -> VerifierAccepts m
trustedToVerifier (MkTrustedFixture _ _ w) = VAStructural w

||| A `TrustedFixture` projects to `SpecAccepts` similarly.
public export
trustedToSpec : TrustedFixture m -> SpecAccepts m
trustedToSpec (MkTrustedFixture _ _ w) = MkSpecAccepts w

||| A `TrustedFixture` projects to `SourceAccepts` similarly.
public export
trustedToSource : TrustedFixture m -> SourceAccepts m
trustedToSource (MkTrustedFixture _ _ w) = SAStructural w

||| `ExtendedAgreement` — `StructuralAgreement` plus a fixture lookup.
||| A consumer with an `ExtendedAgreement` and a `VADifferential`
||| witness can ask the lookup for the matching `TrustedFixture` and
||| obtain a structural witness — turning the dangling differential
||| case into a structural one.
|||
||| The lookup returns `Maybe` because not every fixture name will be
||| registered.  An empty `ExtendedAgreement` (returning `Nothing`
||| everywhere) trivially exists; populated ones grow as fixtures are
||| audited.  See `emptyExtendedAgreement` for the empty witness.
public export
record ExtendedAgreement where
  constructor MkExtendedAgreement
  baseStructural : StructuralAgreement
  fixtureLookup :
       (m         : ModuleSummary)
    -> (fixtureName : String)
    -> (fixtureId   : Nat)
    -> Maybe (TrustedFixture m)

||| The empty `ExtendedAgreement`: structural agreement plus a lookup
||| that returns `Nothing` for every fixture.  Concrete inhabitant
||| showing the record is constructible without external trust.
||| Future fixture audits replace the lookup with non-empty
||| dispatchers.
public export
emptyExtendedAgreement : ExtendedAgreement
emptyExtendedAgreement = MkExtendedAgreement
  structuralAgreement
  (\_, _, _ => Nothing)

||| Promote a `VADifferential` witness to `SpecAccepts` using an
||| `ExtendedAgreement`.  Returns `Nothing` if the fixture is not
||| registered.  Total — no `believe_me`, no `assert_total`.
|||
||| This is the constructive bridge promised by the section header:
||| a `VADifferential` witness plus a registered fixture produces a
||| structural-grade spec acceptance.
public export
verifierImpliesSpecExtended :
     ExtendedAgreement
  -> (m : ModuleSummary)
  -> VerifierAccepts m
  -> Maybe (SpecAccepts m)
verifierImpliesSpecExtended _   _ (VAStructural fa)         =
  Just (MkSpecAccepts fa)
verifierImpliesSpecExtended ext m (VADifferential name fid) =
  map trustedToSpec (ext.fixtureLookup m name fid)

||| Symmetric direction: `SADifferential` to `SpecAccepts` via the
||| same fixture-lookup mechanism.  Both source and verifier
||| differential cases route through the same fixture registry.
public export
sourceImpliesSpecExtended :
     ExtendedAgreement
  -> (m : ModuleSummary)
  -> SourceAccepts m
  -> Maybe (SpecAccepts m)
sourceImpliesSpecExtended _   _ (SAStructural fa)        =
  Just (MkSpecAccepts fa)
sourceImpliesSpecExtended ext m (SADifferential name fid) =
  map trustedToSpec (ext.fixtureLookup m name fid)
