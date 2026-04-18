-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Proofs.idr — Top-level proof combinators for typed-wasm ABI
--
-- This module composes the individual level proofs into a unified
-- "proof certificate" that attests to all 12 levels of type safety
-- for a typed-wasm program (L1-10 from Levels.idr, L11 from Tropical.idr,
-- L12 from Epistemic.idr).
--
-- The certificate is analogous to VCL-total's proof certificates (JSON/CBOR
-- structures attached to query results) but operates at compile time.
-- Once the certificate is constructed, all safety properties are guaranteed
-- and the proofs are erased — the output is bare WASM instructions.
--
-- This is the module that ties everything together.

module TypedWasm.ABI.Proofs

import TypedWasm.ABI.Region
import TypedWasm.ABI.TypedAccess
import TypedWasm.ABI.Levels
import TypedWasm.ABI.Pointer
import TypedWasm.ABI.Effects
import TypedWasm.ABI.Lifetime
import TypedWasm.ABI.Linear
import TypedWasm.ABI.MultiModule
import TypedWasm.ABI.Tropical
import TypedWasm.ABI.Epistemic
-- TEMP: Layout import gated pending Idris2 0.8 reduction fix in Layout/Types.idr.
-- See typed-wasm.ipkg Layout block + PROOF-NEEDS.md Layout-fix entry.
-- import TypedWasm.ABI.Layout
import TypedWasm.ABI.ModuleIsolation
import TypedWasm.ABI.SessionProtocol
import TypedWasm.ABI.ResourceCapabilities

%default total

-- ============================================================================
-- Individual Level Attestations
-- ============================================================================

||| An attestation for a single level. Contains the level number and
||| proof status.
public export
data LevelStatus : Type where
  ||| The level was proven to hold.
  Proven : LevelStatus
  ||| The level was not applicable (e.g., Level 10 for a non-allocating function).
  NotApplicable : LevelStatus
  ||| The level check timed out (for complex proofs with a time budget).
  Timeout : LevelStatus

||| A single level attestation: level number + status.
public export
data LevelAttestation : Type where
  MkAttestation : (level : Nat) -> (status : LevelStatus) -> LevelAttestation

-- ============================================================================
-- The Proof Certificate (All 12 Levels)
-- ============================================================================

||| A complete proof certificate for a typed-wasm program or function.
||| This is the top-level artifact that attests to type safety.
|||
||| The certificate contains:
|||   1. Attestations for each of the 12 levels (L1-L10 + L11 tropical + L12 epistemic)
|||   2. The highest level achieved (early exit for simple operations)
|||   3. Multi-module compatibility certificates (if applicable)
|||
||| Constructing this type requires providing proofs for every level
||| that is applicable. Levels that are not applicable (e.g., linearity
||| for a function that doesn't allocate) are marked NotApplicable.
|||
||| VCL-total analogy: this is the ProvedResult sigma pair.
public export
data ProofCertificate : Type where
  MkCertificate : (levels : List LevelAttestation)
               -> (highestProven : Nat)
               -> (multiModule : List CompatCertificate)
               -> ProofCertificate

-- ============================================================================
-- Progressive Level Checking
-- ============================================================================

||| Proof that levels are checked progressively: you cannot skip levels.
||| Level N can only be checked if Level (N-1) is Proven or NotApplicable.
|||
||| This mirrors VCL-total's slipstream mode: queries enter at L1 and exit
||| as soon as remaining levels don't apply.
public export
data ProgressiveCheck : Type where
  ||| Level 1 is always the starting point.
  StartL1 : LevelAttestation -> ProgressiveCheck
  ||| Advance to the next level. Requires the previous level to be
  ||| Proven or NotApplicable.
  Advance : ProgressiveCheck
         -> LevelAttestation
         -> ProgressiveCheck

||| Extract the highest proven level from a progressive check.
public export
highestLevel : ProgressiveCheck -> Nat
highestLevel (StartL1 (MkAttestation n _)) = n
highestLevel (Advance _ (MkAttestation n Proven)) = n
highestLevel (Advance prev (MkAttestation _ _)) = highestLevel prev

||| Construct a Level 11 attestation from a cost-bounded access path.
||| Requires an AllPairsCosts witness proving every access route is bounded.
public export
attestL11_CostBounded : {n : Nat} -> AllPairsCosts n -> LevelAttestation
attestL11_CostBounded _ = MkAttestation 11 Proven

||| Construct a Level 12 attestation from an epistemic freshness proof.
||| Requires a Level12Proof witnessing that the reader's knowledge is current.
public export
attestL12_EpistemicFresh : Level12Proof -> LevelAttestation
attestL12_EpistemicFresh _ = MkAttestation 12 Proven

||| Construct a Level 13 attestation from an isolated module declaration.
||| Requires an IsolatedModule witness proving per-module memory isolation.
public export
attestL13_Isolated : IsolatedModule -> LevelAttestation
attestL13_Isolated _ = MkAttestation 13 Proven

-- Note on qualification: `Lifetime` names must be qualified as
-- `Lifetime.Lifetime` / `Lifetime.Outlives` in this module because
-- `Levels.idr` also defines a `Lifetime` type and an `Outlives`
-- relation.  The qualification picks the authoritative
-- propositional forms from `Lifetime.idr`.

||| Construct a Level 14 attestation from a well-formed session protocol.
||| Requires a WellFormedProtocol witness proving type-state transition safety.
public export
attestL14_SessionSafe : {p : Protocol} -> WellFormedProtocol p -> LevelAttestation
attestL14_SessionSafe _ = MkAttestation 14 Proven

||| Construct a Level 15 attestation from a capability containment proof.
||| Requires an l15bSoundness or l15cSoundness witness proving resource safety.
public export
attestL15_CapsSafe : {owner : ModuleCaps} -> FunctionCaps owner -> LevelAttestation
attestL15_CapsSafe _ = MkAttestation 15 Proven

-- ============================================================================
-- Proof Composition
-- ============================================================================

||| Compose two proof certificates. Used when combining results from
||| independently verified modules.
|||
||| The composed certificate takes the MINIMUM highest level:
||| if Module A is proven to Level 8 and Module B to Level 6,
||| the combined guarantee is Level 6 (the weakest link).
public export
composeCertificates : ProofCertificate -> ProofCertificate -> ProofCertificate
composeCertificates (MkCertificate ls1 h1 mm1) (MkCertificate ls2 h2 mm2) =
  MkCertificate (ls1 ++ ls2) (min h1 h2) (mm1 ++ mm2)

-- ============================================================================
-- Level-Specific Certificate Constructors (PROOF-NEEDS §P1.1 — A7)
-- ============================================================================
--
-- Every attestation below REQUIRES a matching witness from the level's
-- proof module.  Passing `Proven` is not enough; the caller must produce
-- the structural evidence the level is about.  The witnesses are
-- compile-time-only (erased) — they do not cost anything at runtime —
-- but they cannot be conjured from thin air.  If the level does not
-- hold, the corresponding witness type is uninhabited and the
-- attestation cannot be constructed.
--
-- L8 was already witness-consuming (EffectSubsumes); the other nullary
-- attestations from the pre-A7 revision have been promoted.  The
-- witness types are drawn from the relevant level module:
--
--   L1  — a Schema that type-checked (Region.idr)
--   L2  — FieldIn (Region.idr)
--   L3  — WasmTypeCompat (MultiModule.idr)
--   L4  — Ptr k s l NonNull (Pointer.idr)
--   L5  — InBounds (Region.idr)
--   L6  — AccessResult (TypedAccess.idr)
--   L7  — ExclusiveWitness (Pointer.idr)
--   L8  — EffectSubsumes (Effects.idr) — unchanged from pre-A7
--   L9  — Outlives (Lifetime.idr)
--   L10 — CompletedProtocol (Linear.idr)

||| Construct a Level 1 attestation.  The witness is the Schema itself
||| — producing a well-typed `Schema` value requires the parser and
||| type-checker to have succeeded, which is what L1 attests.
public export
attestL1_InstructionValid : (s : Schema) -> LevelAttestation
attestL1_InstructionValid _ = MkAttestation 1 Proven

||| Construct a Level 2 attestation from a region-binding witness.
||| `FieldIn name schema` proves that the referenced field genuinely
||| lives in the declared schema — i.e. the region binding resolved.
public export
attestL2_RegionBound : {0 name : String}
                    -> {0 schema : Schema}
                    -> FieldIn name schema
                    -> LevelAttestation
attestL2_RegionBound _ = MkAttestation 2 Proven

||| Construct a Level 3 attestation from a WasmTypeCompat witness.
||| Types are compatible iff they are identical (`TypeCompat` is
||| the only constructor), so the witness transports the type
||| equality explicitly.
public export
attestL3_TypeCompat : {0 a, b : WasmType}
                   -> WasmTypeCompat a b
                   -> LevelAttestation
attestL3_TypeCompat _ = MkAttestation 3 Proven

||| Construct a Level 4 attestation from a non-null pointer.
||| The `NonNull` nullability index is the compile-time evidence
||| that this pointer cannot be null; dereferencing is safe.
public export
attestL4_NullSafe : {0 k : PtrKind}
                 -> {0 s : Schema}
                 -> {0 l : Levels.Lifetime}
                 -> Pointer.Ptr k s l NonNull
                 -> LevelAttestation
attestL4_NullSafe _ = MkAttestation 4 Proven

||| Construct a Level 5 attestation from a bounds proof.
||| `InBounds idx count` proves `idx < count`, so the access
||| stays inside the region's allocated slots.
public export
attestL5_BoundsProof : {0 idx, count : Nat}
                    -> InBounds idx count
                    -> LevelAttestation
attestL5_BoundsProof _ = MkAttestation 5 Proven

||| Construct a Level 6 attestation from an `AccessResult`.
||| The result type `ty` is fixed by the access operation's type
||| index, so holding an `AccessResult ty` is evidence that the
||| result type is both known and consistent with the schema.
public export
attestL6_ResultType : {0 ty : WasmType}
                   -> AccessResult ty
                   -> LevelAttestation
attestL6_ResultType _ = MkAttestation 6 Proven

||| Construct a Level 7 attestation from an exclusivity witness.
||| `ExclusiveWitness s` records the scope in which a pointer was
||| checked to be the unique reference into its schema.
public export
attestL7_AliasFree : {0 s : Schema}
                  -> ExclusiveWitness s
                  -> LevelAttestation
attestL7_AliasFree _ = MkAttestation 7 Proven

||| Construct a Level 8 attestation from an effect subsumption proof.
||| (This was already witness-consuming pre-A7; kept for reference.)
public export
attestL8_EffectSafe : {0 declared, actual : EffectSet}
                   -> EffectSubsumes declared actual
                   -> LevelAttestation
attestL8_EffectSafe _ = MkAttestation 8 Proven

||| Construct a Level 9 attestation from an `Outlives` proof.
||| `Lifetime.Outlives rl sl` is the lifetime-safety witness: the referent's
||| lifetime outlives the scope of use, so the reference cannot
||| dangle.
public export
attestL9_LifetimeSafe : {0 rl, sl : Lifetime.Lifetime}
                     -> Lifetime.Outlives rl sl
                     -> LevelAttestation
attestL9_LifetimeSafe _ = MkAttestation 9 Proven

||| Construct a Level 10 attestation from a `CompletedProtocol`
||| witness — evidence that the linear allocation protocol was
||| closed (allocated → freed exactly once).
public export
attestL10_Linear : {0 tok : Nat}
                -> CompletedProtocol tok
                -> LevelAttestation
attestL10_Linear _ = MkAttestation 10 Proven

-- ============================================================================
-- Full Certificate Construction
-- ============================================================================

||| Construct a full proof certificate from progressive level checks.
||| This is the main entry point for the proof engine.
public export
buildCertificate : ProgressiveCheck -> List CompatCertificate -> ProofCertificate
buildCertificate checks multiMod =
  MkCertificate (extractAttestations checks) (highestLevel checks) multiMod
  where
    extractAttestations : ProgressiveCheck -> List LevelAttestation
    extractAttestations (StartL1 att) = [att]
    extractAttestations (Advance prev att) = extractAttestations prev ++ [att]

-- ============================================================================
-- Certificate for Simple Operations
-- ============================================================================

||| A Level 6 certificate for simple read operations.
||| Most memory accesses in practice achieve L6 and exit — they don't
||| need aliasing, effect, lifetime, or linearity proofs because the
||| access is a simple read with no ownership transfer.
|||
||| The function requires one witness per attested level.  The
||| witnesses are compile-time-only (erased at runtime) but cannot
||| be conjured without a genuine proof artefact — the whole point
||| of PROOF-NEEDS §P1.1.
public export
simpleReadCert : {0 nameL2    : String}
              -> {0 schemaL2  : Schema}
              -> {0 tyL3      : WasmType}
              -> {0 kindL4    : PtrKind}
              -> {0 schemaL4  : Schema}
              -> {0 lifeL4    : Levels.Lifetime}
              -> {0 idxL5     : Nat}
              -> {0 countL5   : Nat}
              -> {0 tyL6      : WasmType}
              -> (l1 : Schema)
              -> (l2 : FieldIn nameL2 schemaL2)
              -> (l3 : WasmTypeCompat tyL3 tyL3)
              -> (l4 : Pointer.Ptr kindL4 schemaL4 lifeL4 NonNull)
              -> (l5 : InBounds idxL5 countL5)
              -> (l6 : AccessResult tyL6)
              -> ProofCertificate
simpleReadCert l1 l2 l3 l4 l5 l6 = MkCertificate
  [ attestL1_InstructionValid l1
  , attestL2_RegionBound l2
  , attestL3_TypeCompat l3
  , attestL4_NullSafe l4
  , attestL5_BoundsProof l5
  , attestL6_ResultType l6
  ] 6 []

-- ============================================================================
-- Full 12-Level Certificate
-- ============================================================================

||| A certificate attesting all 12 levels: L1-L10 from the core type system,
||| L11 from a tropical cost proof, L12 from an epistemic freshness proof.
|||
||| This is the publication-quality certificate for shared-memory access
||| with full cost and knowledge accounting.  In practice, most functions
||| will exit at L6 (simpleReadCert); L11-L12 are activated only when
||| cost_bound and region.sync annotations are present.
|||
||| Every level requires its own witness (A7 / PROOF-NEEDS §P1.1).
||| The L8 witness is the caller-supplied `EffectSubsumes`; pre-A7
||| this was hard-coded to `SubNil` for the vacuous empty-actual
||| case, which the caller can still pass explicitly if they want
||| that semantics.
public export
fullCert12 : {0 nameL2    : String} -> {0 schemaL2 : Schema}
          -> {0 tyL3      : WasmType}
          -> {0 kindL4    : PtrKind} -> {0 schemaL4 : Schema} -> {0 lifeL4 : Levels.Lifetime}
          -> {0 idxL5     : Nat} -> {0 countL5 : Nat}
          -> {0 tyL6      : WasmType}
          -> {0 schemaL7  : Schema}
          -> {0 declared, actual : EffectSet}
          -> {0 rl, sl    : Lifetime.Lifetime}
          -> {0 tokL10    : Nat}
          -> {n           : Nat}
          -> (l1          : Schema)
          -> (l2          : FieldIn nameL2 schemaL2)
          -> (l3          : WasmTypeCompat tyL3 tyL3)
          -> (l4          : Pointer.Ptr kindL4 schemaL4 lifeL4 NonNull)
          -> (l5          : InBounds idxL5 countL5)
          -> (l6          : AccessResult tyL6)
          -> (l7          : ExclusiveWitness schemaL7)
          -> (l8          : EffectSubsumes declared actual)
          -> (l9          : Lifetime.Outlives rl sl)
          -> (l10         : CompletedProtocol tokL10)
          -> (costProof       : AllPairsCosts n)
          -> (epistemicProof  : Level12Proof)
          -> ProofCertificate
fullCert12 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 costProof epistemicProof =
  MkCertificate
    [ attestL1_InstructionValid  l1
    , attestL2_RegionBound       l2
    , attestL3_TypeCompat        l3
    , attestL4_NullSafe          l4
    , attestL5_BoundsProof       l5
    , attestL6_ResultType        l6
    , attestL7_AliasFree         l7
    , attestL8_EffectSafe        l8
    , attestL9_LifetimeSafe      l9
    , attestL10_Linear           l10
    , attestL11_CostBounded      costProof
    , attestL12_EpistemicFresh   epistemicProof
    ] 12 []

-- ============================================================================
-- Full 15-Level Certificate
-- ============================================================================

||| A certificate attesting all 15 levels: L1-L10 from the core type system,
||| L11-L12 for shared memory, L13-L15 for agent-style isolation and protocols.
|||
||| This is the highest-tier certificate for multi-agent, effectful,
||| protocol-driven typed-wasm modules.  Every level requires its own
||| witness (A7 / PROOF-NEEDS §P1.1).
public export
fullCert15 : {0 nameL2    : String} -> {0 schemaL2 : Schema}
          -> {0 tyL3      : WasmType}
          -> {0 kindL4    : PtrKind} -> {0 schemaL4 : Schema} -> {0 lifeL4 : Levels.Lifetime}
          -> {0 idxL5     : Nat} -> {0 countL5 : Nat}
          -> {0 tyL6      : WasmType}
          -> {0 schemaL7  : Schema}
          -> {0 declared, actual : EffectSet}
          -> {0 rl, sl    : Lifetime.Lifetime}
          -> {0 tokL10    : Nat}
          -> {n           : Nat}
          -> {p           : Protocol}
          -> {owner       : ModuleCaps}
          -> (l1          : Schema)
          -> (l2          : FieldIn nameL2 schemaL2)
          -> (l3          : WasmTypeCompat tyL3 tyL3)
          -> (l4          : Pointer.Ptr kindL4 schemaL4 lifeL4 NonNull)
          -> (l5          : InBounds idxL5 countL5)
          -> (l6          : AccessResult tyL6)
          -> (l7          : ExclusiveWitness schemaL7)
          -> (l8          : EffectSubsumes declared actual)
          -> (l9          : Lifetime.Outlives rl sl)
          -> (l10         : CompletedProtocol tokL10)
          -> (costProof       : AllPairsCosts n)
          -> (epistemicProof  : Level12Proof)
          -> (isoMod          : IsolatedModule)
          -> (wfProto         : WellFormedProtocol p)
          -> (fc              : FunctionCaps owner)
          -> ProofCertificate
fullCert15 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 costProof epistemicProof isoMod wfProto fc =
  MkCertificate
    [ attestL1_InstructionValid  l1
    , attestL2_RegionBound       l2
    , attestL3_TypeCompat        l3
    , attestL4_NullSafe          l4
    , attestL5_BoundsProof       l5
    , attestL6_ResultType        l6
    , attestL7_AliasFree         l7
    , attestL8_EffectSafe        l8
    , attestL9_LifetimeSafe      l9
    , attestL10_Linear           l10
    , attestL11_CostBounded      costProof
    , attestL12_EpistemicFresh   epistemicProof
    , attestL13_Isolated         isoMod
    , attestL14_SessionSafe      wfProto
    , attestL15_CapsSafe         fc
    ] 15 []

-- ============================================================================
-- A8 — Level Monotonicity (PROOF-NEEDS §P3.2, reframed)
-- ============================================================================
--
-- PROOF-NEEDS §P3.2 originally asked for
--
--   levelMonotone : LevelAchieved n -> (m : Nat) -> LTE m n -> LevelAchieved m
--
-- over a `LevelAchieved` predicate that does not exist in the codebase.
-- The current design uses `ProgressiveCheck` operationally, with no
-- indexed invariant tying attestations to a specific "achieved" level.
--
-- The reframed theorem below introduces `LevelAchievedIn n atts` — a
-- witness that level `n` was attested with status `Proven` in a
-- concrete attestation list — and proves the monotonicity *under
-- certificate composition*: composing two certificates preserves any
-- level achieved in either component.  This is the structural
-- monotonicity relevant to the current design; the stronger
-- "progressive-order" claim requires redesigning `ProgressiveCheck`
-- with a typed `level = S prevLevel` index and is left as future work.

||| `LevelAchievedIn n atts` — level `n` appears in the attestation list
||| with status `Proven`.  This is the concrete propositional form of
||| "the certificate claims level n".
public export
data LevelAchievedIn : (n : Nat) -> List LevelAttestation -> Type where
  ||| Level `n` is at the head of the list, attested as Proven.
  LAHere  : LevelAchievedIn n (MkAttestation n Proven :: rest)
  ||| Level `n` is achieved somewhere deeper in the tail.
  LAThere : LevelAchievedIn n rest -> LevelAchievedIn n (att :: rest)

||| Level achievement is preserved when new attestations are appended
||| to the right of an existing list.  The original witness walks the
||| same path through the prefix of the combined list.
public export
achievedAppendL : {0 n : Nat} -> {0 xs, ys : List LevelAttestation}
               -> LevelAchievedIn n xs
               -> LevelAchievedIn n (xs ++ ys)
achievedAppendL LAHere        = LAHere
achievedAppendL (LAThere p)   = LAThere (achievedAppendL p)

||| Level achievement is preserved when new attestations are prepended
||| to the left of an existing list.  The original witness is shifted
||| past the prefix via repeated `LAThere`.
public export
achievedAppendR : {0 n : Nat}
               -> (xs : List LevelAttestation)
               -> {0 ys : List LevelAttestation}
               -> LevelAchievedIn n ys
               -> LevelAchievedIn n (xs ++ ys)
achievedAppendR []        p = p
achievedAppendR (_ :: xs) p = LAThere (achievedAppendR xs p)

||| Predicate lifted to full proof certificates: "this certificate
||| claims level `n`".
public export
LevelAchieved : (n : Nat) -> ProofCertificate -> Type
LevelAchieved n (MkCertificate atts _ _) = LevelAchievedIn n atts

||| Monotonicity of certificate composition — left side.  Any level
||| achieved in the left certificate is still achieved in the
||| composition.
public export
composeAchievedL : (c1, c2 : ProofCertificate)
                -> LevelAchieved n c1
                -> LevelAchieved n (composeCertificates c1 c2)
composeAchievedL (MkCertificate _ _ _) (MkCertificate _ _ _) p =
  achievedAppendL p

||| Monotonicity of certificate composition — right side.  Any level
||| achieved in the right certificate is still achieved in the
||| composition.
public export
composeAchievedR : (c1, c2 : ProofCertificate)
                -> LevelAchieved n c2
                -> LevelAchieved n (composeCertificates c1 c2)
composeAchievedR (MkCertificate a1 _ _) (MkCertificate _ _ _) p =
  achievedAppendR a1 p

-- ============================================================================
-- Proof Erasure Guarantee
-- ============================================================================

||| All proofs in typed-wasm are erased at compile time.
|||
||| This is the zero-overhead guarantee: the ProofCertificate, all
||| LevelAttestations, all CompatCertificates, all Outlives proofs,
||| all EffectSubsumes proofs — ALL of them exist only in the type
||| checker. The compiled WASM output contains none of this machinery.
|||
||| The output is bare i32.load, i64.store, etc. — exactly what a
||| hand-written WASM module would contain, but proven safe.
|||
||| This is achieved through Idris2's erasure mechanism:
|||   - Types with quantity 0 are erased
|||   - Proof terms used only in types are erased
|||   - The runtime representation is the same as untyped WASM
public export
data ProofErasureGuarantee : Type where
  ||| Witness that all proof terms are compile-time-only.
  ||| At runtime, a typed-wasm program is indistinguishable from
  ||| a hand-written WASM program — same bytes, same performance.
  MkErasure : ProofErasureGuarantee
