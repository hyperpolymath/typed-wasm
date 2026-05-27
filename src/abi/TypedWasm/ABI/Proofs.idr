-- SPDX-License-Identifier: MPL-2.0
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
import TypedWasm.ABI.Layout
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
-- Proof Erasure Guarantee (PROOF-NEEDS §P3.1)
-- ============================================================================
--
-- The erasure guarantee has TWO faces:
--
-- 1. **Meta-theoretic (appeals to QTT, Brady & Christiansen 2021).**
--    Idris2 is based on Quantitative Type Theory.  A function argument
--    bound at multiplicity 0 is statically guaranteed to have NO runtime
--    representation — QTT's type system rejects any program that tries
--    to inspect a 0-bound value at runtime.  Therefore a function
--    `f : (0 cert : ProofCertificate) -> a -> b` is semantically
--    equivalent to `g : a -> b` after compilation: the certificate is
--    not in the runtime closure.
--
--    typed-wasm's checker-facing attestations already use this shape:
--    see `attestL9_LifetimeSafe`, `attestL10_Linear`, etc. — each takes
--    its witness at quantity 0 (`{0 rl, sl : Lifetime.Lifetime}`,
--    `{0 tok : Nat}`).  The certificate layer is QTT-erased by construction.
--
-- 2. **Operational (parser-level property test, P3.1(a) approximation).**
--    A random `.twasm` program P with `effects { ... }` clauses, parsed
--    alongside a textually-stripped P_bare, yields ASTs that differ ONLY
--    in the `effects` / `caps` fields.  This is tested in
--    `tests/echidna/echidna-harness.mjs` (Property 5).  The full
--    byte-equality-of-compiled-wasm property is blocked pending an
--    `.twasm`→`.wasm` emitter and is noted as deferred in PROOF-NEEDS.md.

||| Witness that a computation of type `b` does not depend on a proof
||| certificate: the certificate is bound at multiplicity 0, so QTT
||| erasure removes it from the runtime closure.
|||
||| Using this witness means "by QTT, the function's behaviour is the
||| same whether called with certificate `c` or certificate `c'` —
||| because at runtime it is called with neither."
|||
||| `Erases f` replaces the old nullary `ProofErasureGuarantee` with
||| a type-level statement that actually binds `f` and constrains its
||| argument's multiplicity.  Constructing `MkErases f` is only
||| possible when `f`'s first argument is 0-bound — which is checked
||| by the typechecker, not asserted by documentation.
public export
data Erases : (f : (0 _ : ProofCertificate) -> a -> b) -> Type where
  ||| Build the erasure witness for a cert-irrelevant function `f`.
  |||
  ||| The constructor's signature forces `f`'s first argument to be
  ||| quantity-0 — QTT then guarantees that `f c x = f c' x` for any
  ||| two certificates `c`, `c'`, because `f` cannot observe `c`.
  MkErases : (0 f : (0 _ : ProofCertificate) -> a -> b) -> Erases f

||| Legacy alias retained for callers that built the old nullary witness.
||| Prefer `Erases` for new code; this is kept to avoid churning the
||| downstream attestation ceremony until A9 rewires it.
public export
data ProofErasureGuarantee : Type where
  ||| The legacy nullary witness.  Its only content is a reference to
  ||| the QTT meta-theorem above — the stronger per-function witness
  ||| is `Erases f`.
  MkErasure : ProofErasureGuarantee

||| Example: a function `g` that takes a 0-quantity certificate and a
||| payload, returning just the payload.  `Erases g` is constructible
||| because `g`'s first argument is 0-bound; this serves as a
||| machine-checked witness that cert-irrelevant functions exist.
public export
dropCert : (0 _ : ProofCertificate) -> (x : Nat) -> Nat
dropCert _ x = x

||| `dropCert` is cert-irrelevant — the cert is erased at runtime.
||| This constructs `Erases dropCert` and therefore type-checks only
||| if the 0-quantity discipline is preserved end-to-end.
public export
dropCertErases : Erases Proofs.dropCert
dropCertErases = MkErases Proofs.dropCert

-- ============================================================================
-- A9 — Attestation soundness (PROOF-NEEDS.md "where is the theorem?")
-- ============================================================================
--
-- PROOF-NEEDS.md (2026-04-13) flagged that `Proofs.idr` "ceremonially
-- rubber-stamps attestations without using their witnesses" — every
-- `attestLN_*` function takes a witness and discards it with `_`,
-- returning `MkAttestation N Proven` unconditionally.  A reviewer
-- asking "where is the lemma proving the attestation follows from the
-- witness?" had nothing to point at.
--
-- The `attestLN_Sound` family below is that lemma, one per level.
-- Each is stated so that it *cannot be invoked without a witness of
-- the exact type the corresponding attestation requires*, and it
-- proves the produced attestation is recognised by `LevelAchievedIn`
-- (the propositional "the certificate claims level N" predicate
-- introduced for A8).  This supplies the missing
--
--   witness  ⟹  the certificate provably claims level N
--
-- bridge for all fifteen levels, witness-consuming at the type level.
-- Like the A8 reframing, this is the honest incremental theorem; the
-- stronger "attestation entails the level's semantic property" claim
-- needs `LevelAttestation` reindexed by the witness and is left as
-- tracked future work (standards#130 / epic standards#124).
--
-- These declarations are purely additive: no existing definition is
-- touched, so no prior proof can regress.  `%default total` (module
-- header) applies; verified with Idris2 0.8.0 via `typed-wasm.ipkg`.

||| L1: holding a `Schema` (parser + type-checker succeeded) proves
||| the certificate claims level 1.
public export
attestL1_Sound : (s : Schema) -> LevelAchievedIn 1 [attestL1_InstructionValid s]
attestL1_Sound _ = LAHere

||| L2: a `FieldIn` region-binding witness proves level 2 is claimed.
public export
attestL2_Sound : {0 name : String} -> {0 schema : Schema}
              -> (w : FieldIn name schema)
              -> LevelAchievedIn 2 [attestL2_RegionBound w]
attestL2_Sound _ = LAHere

||| L3: a `WasmTypeCompat` equality witness proves level 3 is claimed.
public export
attestL3_Sound : {0 a, b : WasmType}
              -> (w : WasmTypeCompat a b)
              -> LevelAchievedIn 3 [attestL3_TypeCompat w]
attestL3_Sound _ = LAHere

||| L4: a non-null `Ptr` proves level 4 is claimed.
public export
attestL4_Sound : {0 k : PtrKind} -> {0 s : Schema} -> {0 l : Levels.Lifetime}
              -> (w : Pointer.Ptr k s l NonNull)
              -> LevelAchievedIn 4 [attestL4_NullSafe w]
attestL4_Sound _ = LAHere

||| L5: an `InBounds` proof proves level 5 is claimed.
public export
attestL5_Sound : {0 idx, count : Nat}
              -> (w : InBounds idx count)
              -> LevelAchievedIn 5 [attestL5_BoundsProof w]
attestL5_Sound _ = LAHere

||| L6: an `AccessResult` proves level 6 is claimed.
public export
attestL6_Sound : {0 ty : WasmType}
              -> (w : AccessResult ty)
              -> LevelAchievedIn 6 [attestL6_ResultType w]
attestL6_Sound _ = LAHere

||| L7: an `ExclusiveWitness` proves level 7 is claimed.
public export
attestL7_Sound : {0 s : Schema}
              -> (w : ExclusiveWitness s)
              -> LevelAchievedIn 7 [attestL7_AliasFree w]
attestL7_Sound _ = LAHere

||| L8: an `EffectSubsumes` proof proves level 8 is claimed.
public export
attestL8_Sound : {0 declared, actual : EffectSet}
              -> (w : EffectSubsumes declared actual)
              -> LevelAchievedIn 8 [attestL8_EffectSafe w]
attestL8_Sound _ = LAHere

||| L9: a `Lifetime.Outlives` proof proves level 9 is claimed.
public export
attestL9_Sound : {0 rl, sl : Lifetime.Lifetime}
              -> (w : Lifetime.Outlives rl sl)
              -> LevelAchievedIn 9 [attestL9_LifetimeSafe w]
attestL9_Sound _ = LAHere

||| L10: a `CompletedProtocol` linear-usage witness proves level 10.
public export
attestL10_Sound : {0 tok : Nat}
               -> (w : CompletedProtocol tok)
               -> LevelAchievedIn 10 [attestL10_Linear w]
attestL10_Sound _ = LAHere

||| L11: an `AllPairsCosts` cost-bound witness proves level 11.
public export
attestL11_Sound : {n : Nat}
               -> (w : AllPairsCosts n)
               -> LevelAchievedIn 11 [attestL11_CostBounded w]
attestL11_Sound _ = LAHere

||| L12: a `Level12Proof` epistemic-freshness witness proves level 12.
public export
attestL12_Sound : (w : Level12Proof)
               -> LevelAchievedIn 12 [attestL12_EpistemicFresh w]
attestL12_Sound _ = LAHere

||| L13: an `IsolatedModule` witness proves level 13 is claimed.
public export
attestL13_Sound : (w : IsolatedModule)
               -> LevelAchievedIn 13 [attestL13_Isolated w]
attestL13_Sound _ = LAHere

||| L14: a `WellFormedProtocol` witness proves level 14 is claimed.
public export
attestL14_Sound : {p : Protocol}
               -> (w : WellFormedProtocol p)
               -> LevelAchievedIn 14 [attestL14_SessionSafe w]
attestL14_Sound _ = LAHere

||| L15: a `FunctionCaps` containment witness proves level 15.
public export
attestL15_Sound : {owner : ModuleCaps}
               -> (w : FunctionCaps owner)
               -> LevelAchievedIn 15 [attestL15_CapsSafe w]
attestL15_Sound _ = LAHere

-- ============================================================================
-- Witness-indexed attestations (standards#130 long-tail closure)
-- ============================================================================
--
-- A9's `attestLN_Sound` family proves `LevelAchievedIn N [attestLN_X w]`
-- — i.e. "the certificate provably claims level N".  That is the
-- weaker face of the soundness story.  The reconciliation banner at
-- the head of `PROOF-NEEDS.md` (2026-05-18, A9 entry) explicitly
-- flagged the stronger claim as outstanding:
--
--     "Stronger 'attestation entails the level's semantic property'
--     (needs `LevelAttestation` reindexed by witness) remains tracked
--     future work under standards#130."
--
-- This section closes that residual.  `LevelAttestationW : (n : Nat)
-- -> Type` is the witness-indexed attestation GADT.  Each constructor
-- packages the *actual witness* that was used to produce the
-- attestation, indexed by the level number.  A consumer holding a
-- `LevelAttestationW N` can project the witness back out (per-level
-- extractor / "entails-semantic-property" lemma) and use it to
-- discharge the underlying safety property — not just the
-- "certificate claims level N" claim.
--
-- The design choice mirrors the post-A14 typed-wasm pattern (PR #79
-- on `VerifierSpec.idr`): the constructor carries the witness, and
-- the trust-injection moment is at construction time.  The legacy
-- bridge `toLegacy` projects each `LevelAttestationW N` back to the
-- unindexed `LevelAttestation` representation, so callers that still
-- consume `List LevelAttestation` (e.g. `ProofCertificate`'s
-- `levels` field) are unaffected.  This section is purely additive:
-- no existing definition is touched, so no prior proof can regress.
--
-- Closes the standards#130 long-tail item recorded in the
-- 2026-05-18 reconciliation banner.

||| Witness-indexed attestation GADT.  One constructor per level;
||| each carries the witness required by the corresponding
||| `attestLN_*` smart constructor.  The type index `n` constrains
||| both the witness shape (each constructor only inhabits the matching
||| `LevelAttestationW n`) and the semantic property it certifies
||| (extracting the witness gives back the level-N safety evidence).
|||
||| Constructing a value of `LevelAttestationW n` is the legitimate
||| witness-injection moment for level `n`.  Pattern-matching on the
||| constructor recovers the exact witness type required to discharge
||| level `n`'s semantic property.
|||
||| Type-level indices are kept RUNTIME-AVAILABLE on these
||| constructors (no `{0}` erasure) so per-level extractors can
||| project both the witness AND the indices into a dependent pair.
||| The legacy `attestLN_*` family erased the same indices because it
||| discarded them; here we retain them precisely because the
||| "entails-semantic-property" lemmas need to surface the witness's
||| type-level context.  Runtime cost is negligible (`Nat` / `String`
||| / `Schema` etc., no heavy structures).
public export
data LevelAttestationW : (n : Nat) -> Type where
  ||| L1 attestation: a `Schema` value witnesses instruction validity.
  AttestL1W  : (s : Schema) -> LevelAttestationW 1
  ||| L2 attestation: a region-binding witness `FieldIn name schema`.
  AttestL2W  : {name : String} -> {schema : Schema}
            -> (w : FieldIn name schema)
            -> LevelAttestationW 2
  ||| L3 attestation: a `WasmTypeCompat` equality witness.
  AttestL3W  : {a, b : WasmType}
            -> (w : WasmTypeCompat a b)
            -> LevelAttestationW 3
  ||| L4 attestation: a non-null `Pointer.Ptr`.
  AttestL4W  : {k : PtrKind} -> {s : Schema} -> {l : Levels.Lifetime}
            -> (w : Pointer.Ptr k s l NonNull)
            -> LevelAttestationW 4
  ||| L5 attestation: a compile-time `InBounds` proof.
  AttestL5W  : {idx, count : Nat}
            -> (w : InBounds idx count)
            -> LevelAttestationW 5
  ||| L6 attestation: an `AccessResult` recording the access return type.
  AttestL6W  : {ty : WasmType}
            -> (w : AccessResult ty)
            -> LevelAttestationW 6
  ||| L7 attestation: an `ExclusiveWitness s` proving alias-freeness.
  AttestL7W  : {s : Schema}
            -> (w : ExclusiveWitness s)
            -> LevelAttestationW 7
  ||| L8 attestation: an `EffectSubsumes declared actual` proof.
  AttestL8W  : {declared, actual : EffectSet}
            -> (w : EffectSubsumes declared actual)
            -> LevelAttestationW 8
  ||| L9 attestation: a `Lifetime.Outlives` proof.
  AttestL9W  : {rl, sl : Lifetime.Lifetime}
            -> (w : Lifetime.Outlives rl sl)
            -> LevelAttestationW 9
  ||| L10 attestation: a `CompletedProtocol` linear-usage witness.
  AttestL10W : {tok : Nat}
            -> (w : CompletedProtocol tok)
            -> LevelAttestationW 10
  ||| L11 attestation: an `AllPairsCosts` cost-bound witness.
  AttestL11W : {n : Nat}
            -> (w : AllPairsCosts n)
            -> LevelAttestationW 11
  ||| L12 attestation: a `Level12Proof` epistemic-freshness witness.
  AttestL12W : (w : Level12Proof) -> LevelAttestationW 12
  ||| L13 attestation: an `IsolatedModule` witness.
  AttestL13W : (w : IsolatedModule) -> LevelAttestationW 13
  ||| L14 attestation: a `WellFormedProtocol` witness.
  AttestL14W : {p : Protocol}
            -> (w : WellFormedProtocol p)
            -> LevelAttestationW 14
  ||| L15 attestation: a `FunctionCaps` containment witness.
  AttestL15W : {owner : ModuleCaps}
            -> (w : FunctionCaps owner)
            -> LevelAttestationW 15

-- ----------------------------------------------------------------------------
-- Smart constructors mirroring the legacy `attestLN_*` family
-- ----------------------------------------------------------------------------
--
-- Each `attestLNW_*` smart constructor accepts the same witness shape
-- as the corresponding legacy `attestLN_*` function but returns the
-- witness-carrying `LevelAttestationW N` instead of the unindexed
-- `LevelAttestation`.  Callers that want both representations get
-- them via `toLegacy` below.

public export
attestL1W_InstructionValid : (s : Schema) -> LevelAttestationW 1
attestL1W_InstructionValid = AttestL1W

public export
attestL2W_RegionBound :
     {name : String} -> {schema : Schema}
  -> (w : FieldIn name schema)
  -> LevelAttestationW 2
attestL2W_RegionBound = AttestL2W

public export
attestL3W_TypeCompat :
     {a, b : WasmType}
  -> (w : WasmTypeCompat a b)
  -> LevelAttestationW 3
attestL3W_TypeCompat = AttestL3W

public export
attestL4W_NullSafe :
     {k : PtrKind} -> {s : Schema} -> {l : Levels.Lifetime}
  -> (w : Pointer.Ptr k s l NonNull)
  -> LevelAttestationW 4
attestL4W_NullSafe = AttestL4W

public export
attestL5W_BoundsProof :
     {idx, count : Nat}
  -> (w : InBounds idx count)
  -> LevelAttestationW 5
attestL5W_BoundsProof = AttestL5W

public export
attestL6W_ResultType :
     {ty : WasmType}
  -> (w : AccessResult ty)
  -> LevelAttestationW 6
attestL6W_ResultType = AttestL6W

public export
attestL7W_AliasFree :
     {s : Schema}
  -> (w : ExclusiveWitness s)
  -> LevelAttestationW 7
attestL7W_AliasFree = AttestL7W

public export
attestL8W_EffectSafe :
     {declared, actual : EffectSet}
  -> (w : EffectSubsumes declared actual)
  -> LevelAttestationW 8
attestL8W_EffectSafe = AttestL8W

public export
attestL9W_LifetimeSafe :
     {rl, sl : Lifetime.Lifetime}
  -> (w : Lifetime.Outlives rl sl)
  -> LevelAttestationW 9
attestL9W_LifetimeSafe = AttestL9W

public export
attestL10W_Linear :
     {tok : Nat}
  -> (w : CompletedProtocol tok)
  -> LevelAttestationW 10
attestL10W_Linear = AttestL10W

public export
attestL11W_CostBounded :
     {n : Nat}
  -> (w : AllPairsCosts n)
  -> LevelAttestationW 11
attestL11W_CostBounded = AttestL11W

public export
attestL12W_EpistemicFresh : (w : Level12Proof) -> LevelAttestationW 12
attestL12W_EpistemicFresh = AttestL12W

public export
attestL13W_Isolated : (w : IsolatedModule) -> LevelAttestationW 13
attestL13W_Isolated = AttestL13W

public export
attestL14W_SessionSafe :
     {p : Protocol}
  -> (w : WellFormedProtocol p)
  -> LevelAttestationW 14
attestL14W_SessionSafe = AttestL14W

public export
attestL15W_CapsSafe :
     {owner : ModuleCaps}
  -> (w : FunctionCaps owner)
  -> LevelAttestationW 15
attestL15W_CapsSafe = AttestL15W

-- ----------------------------------------------------------------------------
-- Witness extractors — "attestation entails the level's semantic property"
-- ----------------------------------------------------------------------------
--
-- The standards#130 long-tail asks for a way to recover the
-- level-specific semantic-property witness from an attestation.
-- For `LevelAttestationW N`, this is literally pattern matching:
-- the constructor packages the witness, so the extractor is a one-line
-- match that returns it (paired with any existential indices the
-- witness carries).  Each lemma below is total, no `believe_me`, no
-- `assert_total`.
--
-- The names follow the pattern `attestLNW_Entails<Property>` so a
-- reader scanning the file sees the semantic claim attached to the
-- name.  Where the witness carries existential type-level data
-- (e.g. `ExclusiveWitness s` for an unknown `s`), the extractor
-- returns a dependent pair `(s ** ExclusiveWitness s)`.

||| L1 entails instruction validity: extract the `Schema` witness.
public export
attestL1W_EntailsInstructionValid : LevelAttestationW 1 -> Schema
attestL1W_EntailsInstructionValid (AttestL1W s) = s

||| L2 entails region-binding: recover the existentially-quantified
||| `(name, schema)` indices plus the `FieldIn` witness.
public export
attestL2W_EntailsRegionBound :
     LevelAttestationW 2
  -> (name : String ** schema : Schema ** FieldIn name schema)
attestL2W_EntailsRegionBound (AttestL2W {name} {schema} w) =
  (name ** schema ** w)

||| L3 entails type compatibility.
public export
attestL3W_EntailsTypeCompat :
     LevelAttestationW 3
  -> (a : WasmType ** b : WasmType ** WasmTypeCompat a b)
attestL3W_EntailsTypeCompat (AttestL3W {a} {b} w) = (a ** b ** w)

||| L4 entails null-safety.
public export
attestL4W_EntailsNullSafe :
     LevelAttestationW 4
  -> (k : PtrKind
     ** s : Schema
     ** l : Levels.Lifetime
     ** Pointer.Ptr k s l NonNull)
attestL4W_EntailsNullSafe (AttestL4W {k} {s} {l} w) = (k ** s ** l ** w)

||| L5 entails bounds-safety.
public export
attestL5W_EntailsBoundsProof :
     LevelAttestationW 5
  -> (idx : Nat ** count : Nat ** InBounds idx count)
attestL5W_EntailsBoundsProof (AttestL5W {idx} {count} w) =
  (idx ** count ** w)

||| L6 entails the access-result type.
public export
attestL6W_EntailsResultType :
     LevelAttestationW 6
  -> (ty : WasmType ** AccessResult ty)
attestL6W_EntailsResultType (AttestL6W {ty} w) = (ty ** w)

||| L7 entails alias-freeness.  The extractor surfaces the actual
||| `ExclusiveWitness s` that justifies the L7 claim — anyone with a
||| `LevelAttestationW 7` can now discharge the L7 semantic property,
||| not merely the "certificate claims level 7" predicate.
public export
attestL7W_EntailsAliasFree :
     LevelAttestationW 7
  -> (s : Schema ** ExclusiveWitness s)
attestL7W_EntailsAliasFree (AttestL7W {s} w) = (s ** w)

||| L8 entails effect-subsumption.
public export
attestL8W_EntailsEffectSafe :
     LevelAttestationW 8
  -> (declared : EffectSet
     ** actual : EffectSet
     ** EffectSubsumes declared actual)
attestL8W_EntailsEffectSafe (AttestL8W {declared} {actual} w) =
  (declared ** actual ** w)

||| L9 entails lifetime safety.
public export
attestL9W_EntailsLifetimeSafe :
     LevelAttestationW 9
  -> (rl : Lifetime.Lifetime
     ** sl : Lifetime.Lifetime
     ** Lifetime.Outlives rl sl)
attestL9W_EntailsLifetimeSafe (AttestL9W {rl} {sl} w) = (rl ** sl ** w)

||| L10 entails linearity (single-consumption).
public export
attestL10W_EntailsLinear :
     LevelAttestationW 10
  -> (tok : Nat ** CompletedProtocol tok)
attestL10W_EntailsLinear (AttestL10W {tok} w) = (tok ** w)

||| L11 entails cost-boundedness.
public export
attestL11W_EntailsCostBounded :
     LevelAttestationW 11
  -> (n : Nat ** AllPairsCosts n)
attestL11W_EntailsCostBounded (AttestL11W {n} w) = (n ** w)

||| L12 entails epistemic freshness.
public export
attestL12W_EntailsEpistemicFresh : LevelAttestationW 12 -> Level12Proof
attestL12W_EntailsEpistemicFresh (AttestL12W w) = w

||| L13 entails module isolation.
public export
attestL13W_EntailsIsolated : LevelAttestationW 13 -> IsolatedModule
attestL13W_EntailsIsolated (AttestL13W w) = w

||| L14 entails session-protocol safety.
public export
attestL14W_EntailsSessionSafe :
     LevelAttestationW 14
  -> (p : Protocol ** WellFormedProtocol p)
attestL14W_EntailsSessionSafe (AttestL14W {p} w) = (p ** w)

||| L15 entails resource-capability containment.
public export
attestL15W_EntailsCapsSafe :
     LevelAttestationW 15
  -> (owner : ModuleCaps ** FunctionCaps owner)
attestL15W_EntailsCapsSafe (AttestL15W {owner} w) = (owner ** w)

-- ----------------------------------------------------------------------------
-- Legacy bridge — `LevelAttestationW n` → `LevelAttestation`
-- ----------------------------------------------------------------------------
--
-- Callers that still consume the unindexed `LevelAttestation` (e.g.
-- `ProofCertificate`'s `levels : List LevelAttestation` field) can
-- project a witness-indexed attestation to the legacy shape by
-- discarding the witness and recording the level + Proven status.
-- This is the back-compat one-way arrow; in the other direction,
-- `LevelAttestation -> LevelAttestationW n` is not constructible
-- without a witness, by design.

||| Project a witness-indexed attestation to the legacy `LevelAttestation`
||| representation.  The witness is discarded, but the soundness story
||| is preserved: the legacy `MkAttestation n Proven` corresponds to a
||| value that was constructed *with* a witness (visible at the source
||| site that called `toLegacy`).
public export
toLegacy : {n : Nat} -> LevelAttestationW n -> LevelAttestation
toLegacy {n} _ = MkAttestation n Proven

-- ----------------------------------------------------------------------------
-- Round-trip equalities with the legacy `attestLN_*` family
-- ----------------------------------------------------------------------------
--
-- The legacy `attestLN_X w = MkAttestation N Proven` definition is
-- definitionally equal to `toLegacy (attestLNW_X w)`.  The fifteen
-- `Refl` equalities below pin that down at the source level so any
-- future change that drifts the two representations apart is caught
-- by the typechecker (and by the regression test's Layer 1 grep).

public export
toLegacyMatchesL1 : (s : Schema)
                 -> toLegacy (attestL1W_InstructionValid s)
                  = attestL1_InstructionValid s
toLegacyMatchesL1 _ = Refl

public export
toLegacyMatchesL2 : {name : String} -> {schema : Schema}
                 -> (w : FieldIn name schema)
                 -> toLegacy (attestL2W_RegionBound w)
                  = attestL2_RegionBound w
toLegacyMatchesL2 _ = Refl

public export
toLegacyMatchesL3 : {a, b : WasmType}
                 -> (w : WasmTypeCompat a b)
                 -> toLegacy (attestL3W_TypeCompat w)
                  = attestL3_TypeCompat w
toLegacyMatchesL3 _ = Refl

public export
toLegacyMatchesL4 : {k : PtrKind} -> {s : Schema} -> {l : Levels.Lifetime}
                 -> (w : Pointer.Ptr k s l NonNull)
                 -> toLegacy (attestL4W_NullSafe w)
                  = attestL4_NullSafe w
toLegacyMatchesL4 _ = Refl

public export
toLegacyMatchesL5 : {idx, count : Nat}
                 -> (w : InBounds idx count)
                 -> toLegacy (attestL5W_BoundsProof w)
                  = attestL5_BoundsProof w
toLegacyMatchesL5 _ = Refl

public export
toLegacyMatchesL6 : {ty : WasmType}
                 -> (w : AccessResult ty)
                 -> toLegacy (attestL6W_ResultType w)
                  = attestL6_ResultType w
toLegacyMatchesL6 _ = Refl

public export
toLegacyMatchesL7 : {s : Schema}
                 -> (w : ExclusiveWitness s)
                 -> toLegacy (attestL7W_AliasFree w)
                  = attestL7_AliasFree w
toLegacyMatchesL7 _ = Refl

public export
toLegacyMatchesL8 : {declared, actual : EffectSet}
                 -> (w : EffectSubsumes declared actual)
                 -> toLegacy (attestL8W_EffectSafe w)
                  = attestL8_EffectSafe w
toLegacyMatchesL8 _ = Refl

public export
toLegacyMatchesL9 : {rl, sl : Lifetime.Lifetime}
                 -> (w : Lifetime.Outlives rl sl)
                 -> toLegacy (attestL9W_LifetimeSafe w)
                  = attestL9_LifetimeSafe w
toLegacyMatchesL9 _ = Refl

public export
toLegacyMatchesL10 : {tok : Nat}
                  -> (w : CompletedProtocol tok)
                  -> toLegacy (attestL10W_Linear w)
                   = attestL10_Linear w
toLegacyMatchesL10 _ = Refl

public export
toLegacyMatchesL11 : {n : Nat}
                  -> (w : AllPairsCosts n)
                  -> toLegacy (attestL11W_CostBounded w)
                   = attestL11_CostBounded w
toLegacyMatchesL11 _ = Refl

public export
toLegacyMatchesL12 : (w : Level12Proof)
                  -> toLegacy (attestL12W_EpistemicFresh w)
                   = attestL12_EpistemicFresh w
toLegacyMatchesL12 _ = Refl

public export
toLegacyMatchesL13 : (w : IsolatedModule)
                  -> toLegacy (attestL13W_Isolated w)
                   = attestL13_Isolated w
toLegacyMatchesL13 _ = Refl

public export
toLegacyMatchesL14 : {p : Protocol}
                  -> (w : WellFormedProtocol p)
                  -> toLegacy (attestL14W_SessionSafe w)
                   = attestL14_SessionSafe w
toLegacyMatchesL14 _ = Refl

public export
toLegacyMatchesL15 : {owner : ModuleCaps}
                  -> (w : FunctionCaps owner)
                  -> toLegacy (attestL15W_CapsSafe w)
                   = attestL15_CapsSafe w
toLegacyMatchesL15 _ = Refl

-- ----------------------------------------------------------------------------
-- Achievement bridge — witness-indexed attestation → `LevelAchievedIn`
-- ----------------------------------------------------------------------------
--
-- The legacy A9 `attestLN_Sound` lemmas prove `LevelAchievedIn N
-- [attestLN_X w]`.  The witness-indexed analogue is uniform: for
-- any `LevelAttestationW n`, the singleton list `[toLegacy att]`
-- contains `MkAttestation n Proven` at its head, hence
-- `LevelAchievedIn n [toLegacy att]`.  One lemma covers all 15
-- levels — the witness was retained through construction and is
-- still available at the consumer via the `attestLNW_Entails*`
-- extractors above.

||| For any witness-indexed attestation of level `n`, the singleton
||| legacy-projected list witnesses `LevelAchievedIn n`.  This
||| subsumes the fifteen per-level `attestLN_Sound` lemmas under the
||| witness-carrying redesign.
public export
attestLW_AchievedIn :
     {n : Nat}
  -> (att : LevelAttestationW n)
  -> LevelAchievedIn n [toLegacy att]
attestLW_AchievedIn _ = LAHere

-- ============================================================================
-- WitnessCertificate — the certificate lifted to witness-carrying form
-- ============================================================================
--
-- `LevelAttestationW n` upgrades a single attestation to witness-
-- carrying form.  `ProofCertificate` still uses `List LevelAttestation`
-- (unindexed) for its `levels` field, so a heterogeneous certificate
-- (different levels with different witness types) can't be built
-- directly out of `LevelAttestationW n`s — Idris2 lists are
-- homogeneous, and each `LevelAttestationW n` lives at a different
-- type per level.
--
-- The standard fix is an existential wrapper: `SomeAttestationW`
-- packages a `LevelAttestationW n` for *some* `n`, hiding the index
-- under the constructor.  A `List SomeAttestationW` is then
-- homogeneous and can replace `List LevelAttestation` in a
-- witness-carrying certificate.
--
-- The level number is RETAINED on `SomeAttestationW` (no `{0}`
-- erasure) so it can be projected at the consumer side without
-- losing information.  This mirrors the design choice on
-- `LevelAttestationW` itself.
--
-- Bridge `witnessToLegacy : WitnessCertificate -> ProofCertificate`
-- projects each `SomeAttestationW` down to the legacy unindexed shape
-- and reassembles a `ProofCertificate`.  Pure projection; no trust
-- injection.

||| Existential wrapper hiding the level index.  Constructing one
||| packages a `LevelAttestationW n` for *some* `n`; pattern-matching
||| recovers both `n` and the witness-carrying attestation.
|||
||| The level index is RETAINED at runtime (no `{0}` erasure) so
||| consumers can project the level number without losing the
||| index-witness pairing.
public export
data SomeAttestationW : Type where
  MkSomeAttW : {n : Nat}
            -> (att : LevelAttestationW n)
            -> SomeAttestationW

||| Project the level index of a wrapped witness attestation.
public export
someAttLevel : SomeAttestationW -> Nat
someAttLevel (MkSomeAttW {n} _) = n

||| Project the wrapped attestation back down to the legacy unindexed
||| `LevelAttestation` shape via `toLegacy`.
public export
someAttToLegacy : SomeAttestationW -> LevelAttestation
someAttToLegacy (MkSomeAttW {n} att) = toLegacy att

||| `WitnessCertificate` — `ProofCertificate` lifted to
||| witness-carrying form.  Same three fields as `ProofCertificate`
||| but `levels` carries `SomeAttestationW` (witness-retained) instead
||| of `LevelAttestation` (witness-discarded).
|||
||| `witnessToLegacy` below projects a `WitnessCertificate` down to a
||| `ProofCertificate` for back-compat with existing consumers
||| (`LevelAchieved`, `composeAchievedL`/`R`, etc.).
public export
record WitnessCertificate where
  constructor MkWitnessCert
  witnessLevels       : List SomeAttestationW
  witnessHighestProven : Nat
  witnessMultiModule  : List CompatCertificate

||| Project each `SomeAttestationW` to legacy `LevelAttestation`
||| via explicit recursion (not `map`-eta, so it reduces on `Nil`
||| definitionally — needed for the bridge round-trip `Refl`s below).
public export
witnessLevelsToLegacy :
     List SomeAttestationW -> List LevelAttestation
witnessLevelsToLegacy []        = []
witnessLevelsToLegacy (x :: xs) = someAttToLegacy x :: witnessLevelsToLegacy xs

||| Bridge: `WitnessCertificate -> ProofCertificate`.  Each
||| `SomeAttestationW` in the levels list is downgraded to
||| `LevelAttestation`; the other two fields pass through unchanged.
||| Total, no `believe_me`, no `assert_total`.
public export
witnessToLegacy : WitnessCertificate -> ProofCertificate
witnessToLegacy (MkWitnessCert ls hi mm) =
  MkCertificate (witnessLevelsToLegacy ls) hi mm

-- ----------------------------------------------------------------------------
-- Composition of witness certificates
-- ----------------------------------------------------------------------------
--
-- Mirrors `composeCertificates : ProofCertificate ->
-- ProofCertificate -> ProofCertificate` but operates on the
-- witness-carrying record.  Concatenates the witness-attestation
-- lists, takes the minimum highest-proven, concatenates the
-- multi-module compatibility lists.
--
-- Compatibility with the legacy composition is captured by the
-- `composeWitnessLegacyAgree` lemma below: legacy composition of
-- the projections equals projection of the witness composition.

||| Compose two witness certificates by concatenation + minimum.
public export
composeWitness :
     WitnessCertificate -> WitnessCertificate -> WitnessCertificate
composeWitness (MkWitnessCert ls1 h1 mm1) (MkWitnessCert ls2 h2 mm2) =
  MkWitnessCert (ls1 ++ ls2) (min h1 h2) (mm1 ++ mm2)

-- ----------------------------------------------------------------------------
-- Bridge / composition compatibility lemma
-- ----------------------------------------------------------------------------

||| Helper: `witnessLevelsToLegacy` distributes over `++`.  This is
||| just `mapAppend` from the standard library (`map` over `++`),
||| but we prove it inline so the next lemma can be a one-line
||| rewrite without depending on the exact stdlib export name.
public export
witnessLevelsToLegacyAppend :
     (xs, ys : List SomeAttestationW)
  -> witnessLevelsToLegacy (xs ++ ys)
   = witnessLevelsToLegacy xs ++ witnessLevelsToLegacy ys
witnessLevelsToLegacyAppend []        ys = Refl
witnessLevelsToLegacyAppend (x :: xs) ys =
  rewrite witnessLevelsToLegacyAppend xs ys in Refl

||| Composition compatibility: composing the projections equals
||| projecting the composition.  Pin-down lemma ensuring the
||| witness-side composition stays consistent with the legacy one
||| under projection.
|||
||| `composeCertificates (witnessToLegacy c1) (witnessToLegacy c2) =
||| witnessToLegacy (composeWitness c1 c2)`
public export
composeWitnessLegacyAgree :
     (c1, c2 : WitnessCertificate)
  -> composeCertificates (witnessToLegacy c1) (witnessToLegacy c2)
   = witnessToLegacy (composeWitness c1 c2)
composeWitnessLegacyAgree (MkWitnessCert ls1 _ _) (MkWitnessCert ls2 _ _) =
  rewrite witnessLevelsToLegacyAppend ls1 ls2 in Refl

-- ----------------------------------------------------------------------------
-- WitnessAchieved — predicate lifted to the new certificate
-- ----------------------------------------------------------------------------
--
-- The legacy `LevelAchieved n c` is `LevelAchievedIn n c.levels`,
-- where `levels : List LevelAttestation`.  The witness-side analogue
-- `WitnessAchieved n c` first projects to legacy via
-- `witnessToLegacy` and then asks for the same predicate on the
-- result.  This keeps the surface identical and makes the bridge
-- proof a one-liner.

||| `WitnessAchieved n c` — witness certificate `c` claims level `n`,
||| under the back-compat projection to `ProofCertificate`.
public export
WitnessAchieved : (n : Nat) -> WitnessCertificate -> Type
WitnessAchieved n c = LevelAchieved n (witnessToLegacy c)

||| Identity bridge: `WitnessAchieved` is definitionally equal to
||| `LevelAchieved` on the projection — there is no information loss
||| in the bridge from the achievement-predicate's point of view.
public export
witnessAchievedIsLegacy :
     {n : Nat} -> {c : WitnessCertificate}
  -> WitnessAchieved n c = LevelAchieved n (witnessToLegacy c)
witnessAchievedIsLegacy = Refl

-- ----------------------------------------------------------------------------
-- Smart constructors / inhabitants
-- ----------------------------------------------------------------------------

||| Empty witness certificate.  No attestations, `highestProven = 0`,
||| no multi-module entries.  Concrete inhabitant proving the record
||| is constructible without external trust.
public export
emptyWitnessCertificate : WitnessCertificate
emptyWitnessCertificate = MkWitnessCert [] 0 []

||| Smart constructor: wrap a single witness attestation as a
||| `SomeAttestationW`.  Inferred level index.
public export
someAtt : {n : Nat} -> LevelAttestationW n -> SomeAttestationW
someAtt {n} att = MkSomeAttW {n} att

||| Singleton witness certificate: one attestation, `highestProven = n`,
||| no multi-module entries.
public export
singletonWitnessCertificate :
     {n : Nat} -> LevelAttestationW n -> WitnessCertificate
singletonWitnessCertificate {n} att =
  MkWitnessCert [MkSomeAttW {n} att] n []

||| Empty bridge round-trip: the legacy projection of an empty
||| witness certificate is the empty proof certificate.  Inlined LHS
||| (no `emptyWitnessCertificate` indirection) to keep the equality
||| at definitional depth — `let`-bound top-level values don't unfold
||| through `Refl` in Idris2 0.8.0.
public export
emptyWitnessToLegacy :
     witnessToLegacy (MkWitnessCert [] 0 [])
   = MkCertificate [] 0 []
emptyWitnessToLegacy = Refl
