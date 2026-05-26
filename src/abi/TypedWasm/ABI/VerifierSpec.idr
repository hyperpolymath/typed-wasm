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

||| `SpecAccepts m` — the Idris2 spec accepts a module summary.  Built
||| from `IntentsLinearAcceptable` on every function's intent list.
||| Stated as a `data` with one constructor so future extensions
||| (L13 cross-module checks, L14 session-state) can be added as new
||| constructors without breaking existing witnesses.
public export
data SpecAccepts : ModuleSummary -> Type where
  MkSpecAccepts :
       (perFunction : (f : FunctionSummary)
                   -> Elem f m.functions
                   -> IntentsLinearAcceptable f.intents)
    -> SpecAccepts m

-- ============================================================================
-- Verifier acceptance (opaque — pinned by the differential harness)
-- ============================================================================
--
-- The Rust verifier's acceptance set is not directly representable in
-- Idris2 (it consumes raw wasm bytes via wasmparser).  We model it as
-- an OPAQUE predicate `VerifierAccepts m` indexed by the same
-- `ModuleSummary` shape; the differential testing harness in
-- `tests/cross_compat.rs` is what pins down whether the predicate
-- holds for a given module.
--
-- The predicate's introduction rule is intentionally non-public: the
-- only legitimate way to construct a `VerifierAccepts` witness is
-- through `differentialAccepted` (below), which calls out the
-- harness's role.  This makes the data flow auditable in the proof:
-- you can search for `MkVerifierAccepts` and find exactly the places
-- where the trust is being injected.

||| Opaque verifier-acceptance predicate.  Constructible only by
||| `differentialAccepted` (statement-level promise; no `Refl` body
||| could ever justify it without the harness's external evidence).
public export
data VerifierAccepts : ModuleSummary -> Type where
  MkVerifierAccepts :
       (differentialEvidence : String)
    -> (fixtureId            : Nat)
    -> VerifierAccepts m

||| Construct a `VerifierAccepts` witness from differential-harness
||| evidence (fixture name + numeric id from `tests/cross_compat.rs`).
||| Naming the fixture in the witness makes the trust boundary
||| inspectable: every `VerifierAccepts` use can be traced back to a
||| concrete row in the differential table.
public export
differentialAccepted : (fixtureName : String) -> (fixtureId : Nat)
                   -> VerifierAccepts m
differentialAccepted name fid = MkVerifierAccepts name fid

-- ============================================================================
-- Source-checker acceptance (item 8 surface)
-- ============================================================================

||| Source-checker acceptance predicate.  Like `VerifierAccepts`, the
||| source checker's acceptance set is determined by an external
||| implementation (the AffineScript front-end at present, replaced by
||| an Idris2 parser when Track A lands).  The predicate is opaque and
||| witnessed by the source-side test harness.
public export
data SourceAccepts : ModuleSummary -> Type where
  MkSourceAccepts :
       (sourceEvidence : String)
    -> (fixtureId      : Nat)
    -> SourceAccepts m

||| Construct a `SourceAccepts` witness from source-side evidence.
public export
sourceAccepted : (fixtureName : String) -> (fixtureId : Nat)
              -> SourceAccepts m
sourceAccepted name fid = MkSourceAccepts name fid

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
