-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra/MinMax.idr — the min-max (bottleneck) grade on ℕ ∪ {∞}.
--
-- THE ONE DEFINITION OF THE BOTTLENECK SEQUENCE IN THIS TREE.
-- TypedWasm.ABI.Tropical's `tropMax` (the L11 bottleneck layer,
-- Level11BottleneckProof) is `minMaxSeq`, not a copy of it.
--
-- Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Instances/MinMax.agda @ 0b338c9fc45cd04e7ee7d00b3855cd59d56a2afe
-- Correspondence status: ASSUMED (transcription); the sequence's operation
-- table is TESTED on both sides by tests/transcription.
--
-- Renaming (the only change from the Agda text): _⊔g_ is minMaxSeq; the
-- carrier and the alternatives are Loss's own (Agda imports Loss's Grade,
-- fin / inf and _⊓g_; here LossGrade, Finite / Infinity and lossAlt).
-- Clause order is kept.
--
--   minMaxSeq = sequence     = MAX (the worst hop)       — the "⊗", unit Finite 0
--   lossAlt   = alternatives = MIN (the better path)     — the "⊕", unit Infinity
-- Infinity absorbs under both: an unreachable hop makes the path unreachable,
-- and an unreachable alternative is never chosen.
--
-- The carrier is shared with Loss ON PURPOSE (upstream Morphism.agda,
-- `loss-bottleneck`: the identity on the carrier is a lax morphism Loss →
-- MinMax, because a bottleneck never exceeds the sum).  Idris2 resolves an
-- interface by its carrier, and `ResourceAlgebra LossGrade` is already Loss,
-- so this instance and its layers are NAMED implementations: use them with
-- `@{minMax}`, `@{minMaxDioid}`, ... .  They never take part in search.
--
-- Neither min-plus (sequence is max, not +) nor max-plus (max is the
-- sequence, not the alternatives, and 𝟘 is ∞, not −∞): Separation.idr S-4
-- and tests/reject/MinMaxIsLoss.idr are the checked statements.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra.MinMax

import public Data.Nat
import TypedWasm.ABI.ResourceAlgebra
import TypedWasm.ABI.ResourceAlgebra.Nat
import public TypedWasm.ABI.ResourceAlgebra.Loss

%default total

||| Sequence: the worst hop.  Agda `_⊔g_`.
public export
minMaxSeq : LossGrade -> LossGrade -> LossGrade
minMaxSeq Infinity   _          = Infinity
minMaxSeq (Finite m) Infinity   = Infinity
minMaxSeq (Finite m) (Finite n) = Finite (maximum m n)

-- ============================================================================
-- Sequence: (minMaxSeq, Finite 0) is a monoid
-- ============================================================================

||| Agda `⊔g-assoc`.
public export
minMaxSeqAssoc : (a, b, c : LossGrade) ->
                 minMaxSeq (minMaxSeq a b) c = minMaxSeq a (minMaxSeq b c)
minMaxSeqAssoc (Finite a) (Finite b) (Finite c) = cong Finite (maxAssoc a b c)
minMaxSeqAssoc (Finite a) (Finite b) Infinity   = Refl
minMaxSeqAssoc (Finite a) Infinity   c          = Refl
minMaxSeqAssoc Infinity   b          c          = Refl

||| Agda `⊔g-unitˡ`.
public export
minMaxSeqUnitL : (a : LossGrade) -> minMaxSeq (Finite 0) a = a
minMaxSeqUnitL (Finite a) = Refl
minMaxSeqUnitL Infinity   = Refl

||| Agda `⊔g-unitʳ`.
public export
minMaxSeqUnitR : (a : LossGrade) -> minMaxSeq a (Finite 0) = a
minMaxSeqUnitR (Finite a) = cong Finite (maximumZeroNLeft a)
minMaxSeqUnitR Infinity   = Refl

-- ============================================================================
-- The instance, and its layers
-- ============================================================================

||| Agda `MinMax : ResourceAlgebra`.  Named: the carrier is Loss's.
public export
[minMax] ResourceAlgebra LossGrade where
  oplus    = lossAlt
  otimes   = minMaxSeq
  zeroG    = Infinity
  oneG     = Finite 0
  altAssoc = lossAltAssoc
  altComm  = lossAltComm
  altIdem  = lossAltIdem
  altUnitL = \_ => Refl
  seqAssoc = minMaxSeqAssoc
  seqUnitL = minMaxSeqUnitL
  seqUnitR = minMaxSeqUnitR

||| Agda `MinMax-dioid` (distribˡ).
public export
minMaxDistribL : (a, b, c : LossGrade) ->
                 minMaxSeq a (lossAlt b c) = lossAlt (minMaxSeq a b) (minMaxSeq a c)
minMaxDistribL (Finite a) (Finite b) (Finite c) = cong Finite (maxDistribLMin a b c)
minMaxDistribL (Finite a) (Finite b) Infinity   = Refl
minMaxDistribL (Finite a) Infinity   c          = Refl
minMaxDistribL Infinity   b          c          = Refl

||| Agda `MinMax-dioid` (distribʳ).
public export
minMaxDistribR : (a, b, c : LossGrade) ->
                 minMaxSeq (lossAlt a b) c = lossAlt (minMaxSeq a c) (minMaxSeq b c)
minMaxDistribR (Finite a) (Finite b) (Finite c) = cong Finite (maxDistribRMin a b c)
minMaxDistribR (Finite a) (Finite b) Infinity   = Refl
minMaxDistribR (Finite a) Infinity   (Finite c) = Refl
minMaxDistribR (Finite a) Infinity   Infinity   = Refl
minMaxDistribR Infinity   b          c          = Refl

||| Agda `MinMax-dioid`.
public export
[minMaxDioid] IsDioid LossGrade using minMax where
  distribL = minMaxDistribL
  distribR = minMaxDistribR

||| Agda `MinMax-ordered = IsDioid.ordered MinMax-dioid`.
public export
[minMaxOrdered] IsOrdered LossGrade using minMax where
  otimesMonoL = dioidMonoL @{minMaxDioid}
  otimesMonoR = dioidMonoR @{minMaxDioid}

||| Agda `MinMax-annihilating` (annihilʳ).
public export
minMaxAnnihilR : (a : LossGrade) -> minMaxSeq a Infinity = Infinity
minMaxAnnihilR (Finite _) = Refl
minMaxAnnihilR Infinity   = Refl

||| Agda `MinMax-annihilating`.
public export
[minMaxAnnihilating] IsAnnihilating LossGrade using minMax where
  annihilL = \_ => Refl
  annihilR = minMaxAnnihilR
