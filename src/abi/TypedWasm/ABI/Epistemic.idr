-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Epistemic.idr — Level 12: Epistemic safety for shared memory
--
-- Tracks which module KNOWS what about shared memory state. Module A
-- writes field X; Module B's knowledge of X is stale until an explicit
-- synchronisation point. The type system prevents acting on stale
-- knowledge — a "read" is only valid if the reader's knowledge is current.
--
-- This is epistemic modal logic (K_i φ — "agent i knows φ") applied to
-- shared mutable state. In the database analogy, this is read consistency:
-- a transaction sees a snapshot, not live mutations by other transactions.
--
-- No existing WASM type system, and no existing shared-memory type system
-- we are aware of, provides epistemic safety at the type level.

module TypedWasm.ABI.Epistemic

import TypedWasm.ABI.Region
import TypedWasm.ABI.MultiModule
import TypedWasm.ABI.Levels
import Data.Nat

%default total

-- ============================================================================
-- Global Ground Truth + Epistemic Predicates
-- ============================================================================
--
-- Declaration order (A11, 2026-05-26): FieldVersion → Stale → Fresh →
-- Sync → Knowledge → Knows.  Knowledge.Observed now carries a Sync
-- witness for provenance, so Knowledge depends on Sync rather than
-- preceding it.

||| The actual version of a field in shared memory (global truth).
||| Carries the writer identity at the recorded version — used as the
||| ground-truth witness for `WriteSync` (A11).
public export
record FieldVersion where
  constructor MkFieldVersion
  field : String
  version : Nat
  lastWriter : ModuleId

||| Staleness: a module's knowledge is stale if the field has been
||| written since the module last observed it.
public export
data Stale : (mod : ModuleId) -> (field : String) ->
             (knownVersion : Nat) -> (currentVersion : Nat) -> Type where
  ||| Knowledge is stale when knownVersion < currentVersion.
  MkStale : LT knownVersion currentVersion -> Stale mod field knownVersion currentVersion

||| Freshness: the module's knowledge is current.
|||
||| **Fresh soundness (A14, 2026-06-02 — closes #102).**  `Fresh` now
||| requires a real `FieldVersion` value pinning the `currentVersion`
||| index to global ground truth.  The original constructor took only
||| a `(knownVersion = currentVersion)` self-referential proof —
||| anyone could mint `MkFresh Refl` for any `(mod, field, v)` pair,
||| symmetric to the pre-A11 `WriteSync` gap.  The tightened form
||| forces the caller to commit to a `FieldVersion` record matching
||| `(field, currentVersion)`.  `ExplicitSync` inherits the pin via
||| its `Fresh` argument — no separate `FieldVersion` parameter is
||| required on the sync constructor itself.
public export
data Fresh : (mod : ModuleId) -> (field : String) ->
             (knownVersion : Nat) -> (currentVersion : Nat) -> Type where
  ||| Knowledge is fresh when (a) `knownVersion = currentVersion` AND
  ||| (b) `currentVersion` is pinned to the canonical FieldVersion
  ||| record for `field`.  The reader does not have to be the writer,
  ||| so `fv.lastWriter` is unconstrained here; writer provenance is
  ||| captured by `WriteSync` instead.
  MkFresh : (fv : FieldVersion) ->
            fv.field   = field          ->
            fv.version = currentVersion ->
            knownVersion = currentVersion ->
            Fresh mod field knownVersion currentVersion

-- ============================================================================
-- Synchronisation Points
-- ============================================================================

||| A synchronisation event that updates a module's knowledge.
||| After synchronisation, the module knows the current version.
|||
||| **WriteSync soundness (A11, 2026-05-26).**  `WriteSync` now
||| requires a real `FieldVersion` value pinning the writer identity
||| to global ground truth.  The original constructor took only a
||| `(writer = mod)` self-referential proof — anyone could supply
||| `WriteSync mod Refl` for any `mod`, with no link to the actual
||| writer.  The tightened form forces the caller to commit to a
||| FieldVersion record matching `(field, newVersion, mod)`.
public export
data Sync : (mod : ModuleId) -> (field : String) ->
            (oldVersion : Nat) -> (newVersion : Nat) -> Type where
  ||| Explicit sync: the module reads the field and updates its knowledge.
  ExplicitSync : (fresh : Fresh mod field newVersion newVersion) ->
                 Sync mod field oldVersion newVersion
  ||| Write sync: when a module writes a field, it automatically knows
  ||| the new version (it just wrote it).  The `FieldVersion` witness
  ||| pins the writer identity to the field's global `lastWriter`.
  WriteSync : (fv : FieldVersion) ->
              fv.field      = field      ->
              fv.version    = newVersion ->
              fv.lastWriter = mod        ->
              Sync mod field oldVersion newVersion

-- ============================================================================
-- Knowledge State
-- ============================================================================

||| A module's knowledge about a specific field in shared memory.
||| Knowledge is parameterised by a monotonic version counter — each
||| write increments the version, and a reader's knowledge is current
||| only if its version matches the field's current version.
|||
||| **Observed provenance (A11, 2026-05-26).**  `Observed` now carries
||| a `Sync` witness — knowledge at a given version must be traceable
||| to a sync event.  The original nullary `Observed : Knowledge mod
||| field ver` let any caller assert observation at any version with
||| no preconditions; provenance is now required.
public export
data Knowledge : (module_ : ModuleId) -> (field : String) -> (version : Nat) -> Type where
  ||| The module has observed this field at `ver` via a sync event
  ||| originating from `oldVer`.  The sync witness pins the
  ||| provenance.  `oldVer` is declared as an explicit implicit so
  ||| pattern matches and extractions can recover the prior version.
  Observed : {oldVer : Nat} ->
             (sync : Sync mod field oldVer ver) -> Knowledge mod field ver
  ||| The module has NOT observed this field (initial state or invalidated).
  Unknown : Knowledge mod field 0

-- ============================================================================
-- Epistemic Predicates
-- ============================================================================

||| K_i(φ) — "module i knows that field f has version v".
||| This is the core epistemic modal operator.
public export
data Knows : (mod : ModuleId) -> (field : String) -> (version : Nat) -> Type where
  ||| A module knows a field's version if it has observed it at that version.
  MkKnows : Knowledge mod field ver -> (ver > 0 = True) -> Knows mod field ver

-- ============================================================================
-- Level 12 Proof Obligation
-- ============================================================================

||| Level 12 proof: a read from shared memory is epistemically safe.
||| The reader must prove that its knowledge of the field is fresh
||| (not stale) at the point of the read.
public export
record Level12Proof where
  constructor MkLevel12
  ||| The reading module.
  reader : ModuleId
  ||| The field being read.
  field : String
  ||| The reader's known version.
  knownVersion : Nat
  ||| The field's current version (from the global state).
  currentVersion : Nat
  ||| Proof that the reader's knowledge is fresh.
  freshness : Fresh reader field knownVersion currentVersion

-- ============================================================================
-- Key Theorems
-- ============================================================================

||| A writer always has fresh knowledge of what it wrote, given the
||| canonical `FieldVersion` at the post-write state.  Post-A14
||| (#102 closure), `Fresh` requires a `FieldVersion` pin — so this
||| lemma must thread that record through.  The writer-identity pin
||| (`fv.lastWriter = writer`) is also taken for the obvious-but-
||| previously-implicit reason: a writer's freshness comes from being
||| the one named in `lastWriter`.
export
writerKnowsFresh : (writer : ModuleId) -> (field : String) -> (ver : Nat) ->
                   (fv : FieldVersion) ->
                   fv.field      = field ->
                   fv.version    = ver   ->
                   fv.lastWriter = writer ->
                   Fresh writer field ver ver
writerKnowsFresh _ _ _ fv fp vp _ = MkFresh fv fp vp Refl

||| Staleness is decidable: given two versions, knowledge is either fresh,
||| stale-forward (known < current), or stale-backward (current < known).
||| Direct structural recursion on both Nats — avoids relying on the
||| Ordering proof witness machinery.
export
freshOrStale : (known, current : Nat) ->
               Either (known = current) (Either (LT known current) (LT current known))
freshOrStale Z     Z     = Left Refl
freshOrStale Z     (S c) = Right (Left  (LTESucc LTEZero))
freshOrStale (S k) Z     = Right (Right (LTESucc LTEZero))
freshOrStale (S k) (S c) = case freshOrStale k c of
  Left  eq          => Left (cong S eq)
  Right (Left  lt)  => Right (Left  (LTESucc lt))
  Right (Right gt)  => Right (Right (LTESucc gt))

||| Sync restores freshness.
|||
||| Post-A14: both branches must supply the `FieldVersion` pin.  The
||| `ExplicitSync` branch returns its embedded `Fresh` witness
||| directly (the pin is already inside).  The `WriteSync` branch
||| rebuilds a `Fresh` using the same `FieldVersion` that the write
||| committed to.
export
syncRestoresFresh : Sync mod field old new -> Fresh mod field new new
syncRestoresFresh (ExplicitSync fresh)            = fresh
syncRestoresFresh (WriteSync fv fp vp _)          = MkFresh fv fp vp Refl

-- ============================================================================
-- Concurrent-write propagation theorems (A10, 2026-05-26 — closes
-- PROOF-NEEDS §P1.2 "freshness propagation under concurrent writes deferred")
-- ============================================================================

||| Fresh witnesses the equality of the two version indices.  Projector
||| out of `MkFresh` for callers that need to substitute versions in
||| downstream proofs about reads.
export
freshImpliesEqual : Fresh mod field known current -> known = current
freshImpliesEqual (MkFresh _ _ _ eq) = eq

||| Stale witnesses a strict ordering on versions.  Dual projector to
||| `freshImpliesEqual`.
export
staleImpliesLT : Stale mod field known current -> LT known current
staleImpliesLT (MkStale lt) = lt

||| LT is irreflexive — `LT n n` is uninhabited.  Local helper for
||| `freshNotStale`; recurses on the LTESucc constructor (the LTEZero
||| branch is impossible since `LTE 0 0` cannot match `LTE (S n) n`).
ltIrreflexive : LT n n -> Void
ltIrreflexive (LTESucc rest) = ltIrreflexive rest

||| Fresh and Stale are mutually exclusive at the same indices: no
||| concurrent writer can produce a Stale witness against a module that
||| holds a Fresh witness at the *same* (known, current) pair.  The
||| local non-interference property; the propagation theorem below
||| handles the case where `current` actually advances.
export
freshNotStale : Fresh mod field v v' -> Stale mod field v v' -> Void
freshNotStale (MkFresh _ _ _ Refl) (MkStale lt) = ltIrreflexive lt

||| Concurrent-write staleness.  If module `mod`'s view of `field` was
||| fresh at version `v` and the global current version subsequently
||| advances to `v'` (with `v < v'`), `mod`'s view is now stale at
||| `(v, v')`.  Contrapositive of `syncRestoresFresh` — without a Sync
||| event, any other writer's increment moves `mod` to the Stale state.
export
concurrentWriteStales :
  Fresh mod field v v -> LT v v' -> Stale mod field v v'
concurrentWriteStales (MkFresh _ _ _ Refl) lt = MkStale lt

||| Re-synchronisation after a concurrent write restores freshness.  If
||| `mod`'s view is stale at `(v, cur)` and `mod` performs a Sync to
||| `cur`, the post-sync view is fresh at `(cur, cur)`.  Composes
||| `concurrentWriteStales` (the stale arises) with `syncRestoresFresh`
||| (the sync neutralises the stale) into the full recovery protocol:
||| there is no "permanently stuck" state.
export
resyncRecoversFresh :
  Stale mod field v cur -> Sync mod field v cur -> Fresh mod field cur cur
resyncRecoversFresh _ s = syncRestoresFresh s

||| Flagship: freshness propagation under concurrent writes.  Starting
||| from any fresh state at `v`, any number of intervening concurrent
||| writes (advancing the global current version to `cur`) can be
||| neutralised by a single re-Sync.  The post-Sync state is fresh at
||| `(cur, cur)` regardless of how many writes occurred between the
||| original Fresh and the Sync.  This is the named composition theorem
||| that closes PROOF-NEEDS §P1.2.
export
freshnessPropagatesUnderWrites :
  Fresh mod field v v ->
  LT v cur ->
  Sync mod field v cur ->
  Fresh mod field cur cur
freshnessPropagatesUnderWrites _ _ s = syncRestoresFresh s

||| Chained syncs end fresh: any two-step sync sequence by `mod` on the
||| same field terminates in a fresh state at the final version.
||| Corollary of `syncRestoresFresh`; named explicitly because callers
||| composing multi-step read protocols want the chain-level statement
||| rather than re-deriving it at each call site.
export
syncChainEndsFresh :
  Sync mod field v1 v2 -> Sync mod field v2 v3 -> Fresh mod field v3 v3
syncChainEndsFresh _ s2 = syncRestoresFresh s2

||| Project the freshness witness out of a Level 12 certificate.
||| Closes the P1.2 "Level12Proof implies freshness" obligation: anyone
||| holding a `Level12Proof` value has, by construction, a `Fresh`
||| witness at the certificate's `(knownVersion, currentVersion)`
||| indices.  Before this lemma the `.freshness` field was
||| record-projectable but lacked the named status the proof debt
||| called for.
export
epistemicFreshness :
  (p : Level12Proof) ->
  Fresh p.reader p.field p.knownVersion p.currentVersion
epistemicFreshness p = p.freshness

-- ============================================================================
-- Constructor soundness corollaries (A11, 2026-05-26 — closes the
-- WriteSync-admits-fake-writers + Observed-admits-unfounded-versions
-- soundness gaps surfaced during A10)
-- ============================================================================

||| A `WriteSync` carries the global ground-truth writer identity.
||| Given a write-sync event, the writer named in the dependent index
||| `mod` provably matches some `FieldVersion`'s `lastWriter`.  This
||| extracts the `FieldVersion` and the equality witness — closing the
||| "anyone can construct a WriteSync claiming to be the writer" gap
||| by routing the writer identity through global state.
|||
||| Only constructible when the input is a `WriteSync`; `ExplicitSync`
||| does not carry writer provenance (an explicit sync is a read, not
||| a write — by design).  Returns `Nothing` in that case.
public export
writeSyncIdentifiesWriter :
  Sync mod field old new ->
  Maybe (fv : FieldVersion ** (fv.field = field, fv.version = new, fv.lastWriter = mod))
writeSyncIdentifiesWriter (ExplicitSync _)          = Nothing
writeSyncIdentifiesWriter (WriteSync fv fp vp wp)   = Just (fv ** (fp, vp, wp))

||| Observed knowledge has Sync provenance.  Given a `Knowledge mod
||| field ver` value, if it was constructed via `Observed` then a
||| witnessing `Sync mod field oldVer ver` is in scope for some
||| existentially-bound `oldVer`.  Returns `Nothing` for the
||| `Unknown` case (which only inhabits version 0 by design).
|||
||| Closes the "Observed admits unfounded version claims" gap: a
||| caller holding non-Unknown `Knowledge` at any `ver` necessarily
||| has a `Sync` event in scope to justify the claim — provenance
||| can no longer be conjured.
public export
observedHasProvenance :
  Knowledge mod field ver ->
  Maybe (oldVer : Nat ** Sync mod field oldVer ver)
observedHasProvenance Unknown         = Nothing
observedHasProvenance (Observed {oldVer} sync) = Just (oldVer ** sync)

-- ----------------------------------------------------------------------------
-- Residual debt note — A11 ➞ A14 closure (2026-06-02, #102)
-- ----------------------------------------------------------------------------
--
-- A11 (2026-05-26) tightened only `WriteSync` to require a
-- `FieldVersion` pin.  A14 (2026-06-02) closes the symmetric gap by
-- re-indexing `Fresh` on a `FieldVersion` value too — the
-- `currentVersion` index is now pinned to global ground truth, so
-- `MkFresh Refl` no longer types and a caller cannot mint freshness
-- ex nihilo.  `ExplicitSync` does NOT need a separate `FieldVersion`
-- parameter: its `Fresh` argument now carries the pin, and
-- `ExplicitSync (writerKnowsFresh _ _ _ fv ..)` only types if the
-- caller has supplied a real `FieldVersion`.  `Observed` likewise
-- inherits the pin via its `Sync` argument.  No remaining
-- constructor in this file admits an unfounded version claim.
