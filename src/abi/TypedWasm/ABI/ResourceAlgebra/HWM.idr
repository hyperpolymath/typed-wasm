-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra/HWM.idr — the occupancy grade: high-water mark (peak, drift).
--
-- STATUS (inherited from the source): DESIGNED as occupancy-types' algebra
-- (resource-algebra H-2); PROVEN against the definition below.
--
-- Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Instances/HWM.agda @ 0b338c9fc45cd04e7ee7d00b3855cd59d56a2afe
-- (unchanged since cf9235c, the pin it was first transcribed at)
-- Correspondence status: ASSUMED (transcription); operation table TESTED on
-- both sides by tests/transcription.  occupancy-types @ af95728 builds its
-- reclamation law (OccupancyTypes/Reclaim.agda) on that same Agda module.
--
-- The model: a grade records the peak live state reached during a run and
-- the drift (live state still held at the end).  Sequencing b after a starts
-- b from a's drift, so the peak of a;b is  max (peak a) (drift a + peak b) —
-- this is where an occupancy bound stops being a cost bound (a cost would add
-- the peaks).  Drift is non-negative (drift ≤ peak is a field); a signed drift
-- is a recorded extension upstream (H-2).
--
-- Renaming: constructor hwm is MkHWM; _⊗h_ / _⊕h_ / 𝟘h are hwmSeq / hwmAlt /
-- hwmZero.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra.HWM

-- Re-exported so a consumer can REDUCE these grades at type level (the
-- definitions below unfold to Data.Nat and to ResourceAlgebra.Nat's lemmas).
import public Data.Nat
import TypedWasm.ABI.ResourceAlgebra
import public TypedWasm.ABI.ResourceAlgebra.Nat

%default total

||| A high-water-mark grade.  Agda `record Grade` (constructor `hwm`).
public export
record HWMGrade where
  constructor MkHWM
  ||| Peak live state reached during the run.
  peak    : Nat
  ||| Live state still held at the end of the run.
  drift   : Nat
  ||| A run cannot end holding more than its peak.
  bounded : LTE drift peak

||| A grade is determined by peak and drift.  Agda `hwm-≡`.
public export
hwmEq : {p, p', n, n' : Nat} -> {b : LTE n p} -> {b' : LTE n' p'} ->
        p = p' -> n = n' -> MkHWM p n b = MkHWM p' n' b'
hwmEq {b} {b'} Refl Refl = cong (MkHWM _ _) (lteIrrelevant b b')

-- ============================================================================
-- Operations
-- ============================================================================

||| Sequence: the suffix starts from the prefix's drift.  Agda `_⊗h_`.
public export
hwmSeq : HWMGrade -> HWMGrade -> HWMGrade
hwmSeq (MkHWM p1 n1 b1) (MkHWM p2 n2 b2) =
  MkHWM (maximum p1 (n1 + p2)) (n1 + n2)
        (lteTrans (plusMonoRLTE n1 b2) (maximumRightUpperBound p1 (n1 + p2)))

||| Alternatives: componentwise max.  Agda `_⊕h_`.
public export
hwmAlt : HWMGrade -> HWMGrade -> HWMGrade
hwmAlt (MkHWM p1 n1 b1) (MkHWM p2 n2 b2) =
  MkHWM (maximum p1 p2) (maximum n1 n2) (maxMonoLTE b1 b2)

||| Nothing allocated, nothing held: both units.  Agda `𝟘h`.
public export
hwmZero : HWMGrade
hwmZero = MkHWM 0 0 LTEZero

-- ============================================================================
-- Alternatives: componentwise max
-- ============================================================================

||| Agda `⊕h-assoc`.
public export
hwmAltAssoc : (a, b, c : HWMGrade) -> hwmAlt (hwmAlt a b) c = hwmAlt a (hwmAlt b c)
hwmAltAssoc (MkHWM p n _) (MkHWM p' n' _) (MkHWM p'' n'' _) =
  hwmEq (maxAssoc p p' p'') (maxAssoc n n' n'')

||| Agda `⊕h-comm`.
public export
hwmAltComm : (a, b : HWMGrade) -> hwmAlt a b = hwmAlt b a
hwmAltComm (MkHWM p n _) (MkHWM p' n' _) =
  hwmEq (maximumCommutative p p') (maximumCommutative n n')

||| Agda `⊕h-idem`.
public export
hwmAltIdem : (a : HWMGrade) -> hwmAlt a a = a
hwmAltIdem (MkHWM p n _) = hwmEq (maximumIdempotent p) (maximumIdempotent n)

||| Agda `⊕h-unitˡ`.
public export
hwmAltUnitL : (a : HWMGrade) -> hwmAlt HWM.hwmZero a = a
hwmAltUnitL (MkHWM p n _) = hwmEq Refl Refl

-- ============================================================================
-- Sequence
-- ============================================================================

||| Agda `⊗h-assoc`.
public export
hwmSeqAssoc : (a, b, c : HWMGrade) -> hwmSeq (hwmSeq a b) c = hwmSeq a (hwmSeq b c)
hwmSeqAssoc (MkHWM p1 n1 _) (MkHWM p2 n2 _) (MkHWM p3 n3 _) =
  hwmEq
    (trans (cong (maximum (maximum p1 (n1 + p2))) (plusAssoc n1 n2 p3))
    (trans (maxAssoc p1 (n1 + p2) (n1 + (n2 + p3)))
           (cong (maximum p1) (sym (plusDistribLMax n1 p2 (n2 + p3))))))
    (plusAssoc n1 n2 n3)

||| Agda `⊗h-unitˡ`.
public export
hwmSeqUnitL : (a : HWMGrade) -> hwmSeq HWM.hwmZero a = a
hwmSeqUnitL (MkHWM p n _) = hwmEq Refl Refl

||| Agda `⊗h-unitʳ`.
public export
hwmSeqUnitR : (a : HWMGrade) -> hwmSeq a HWM.hwmZero = a
hwmSeqUnitR (MkHWM p n b) =
  hwmEq (trans (cong (maximum p) (plusZeroRightNeutral n)) (maxAbsorbLTE b))
        (plusZeroRightNeutral n)

-- ============================================================================
-- The instance, and its layers
-- ============================================================================

||| Agda `HWM : ResourceAlgebra`.  𝟘 and 𝟙 are the same grade.
public export
ResourceAlgebra HWMGrade where
  oplus    = hwmAlt
  otimes   = hwmSeq
  zeroG    = hwmZero
  oneG     = hwmZero
  altAssoc = hwmAltAssoc
  altComm  = hwmAltComm
  altIdem  = hwmAltIdem
  altUnitL = hwmAltUnitL
  seqAssoc = hwmSeqAssoc
  seqUnitL = hwmSeqUnitL
  seqUnitR = hwmSeqUnitR

||| Agda `HWM-dioid` (distribˡ).
public export
hwmDistribL : (a, b, c : HWMGrade) ->
              hwmSeq a (hwmAlt b c) = hwmAlt (hwmSeq a b) (hwmSeq a c)
hwmDistribL (MkHWM p n _) (MkHWM p2 n2 _) (MkHWM p3 n3 _) =
  hwmEq (trans (cong (maximum p) (plusDistribLMax n p2 p3))
               (sym (maxDup p (n + p2) (n + p3))))
        (plusDistribLMax n n2 n3)

||| Agda `HWM-dioid` (distribʳ).
public export
hwmDistribR : (a, b, c : HWMGrade) ->
              hwmSeq (hwmAlt a b) c = hwmAlt (hwmSeq a c) (hwmSeq b c)
hwmDistribR (MkHWM p2 n2 _) (MkHWM p3 n3 _) (MkHWM p n _) =
  hwmEq (trans (cong (maximum (maximum p2 p3)) (plusDistribRMax n2 n3 p))
               (maxInterchange p2 p3 (n2 + p) (n3 + p)))
        (plusDistribRMax n2 n3 n)

||| Agda `HWM-dioid`.
public export
IsDioid HWMGrade where
  distribL = hwmDistribL
  distribR = hwmDistribR

||| Agda `HWM-ordered = IsDioid.ordered HWM-dioid`.
public export
IsOrdered HWMGrade where
  otimesMonoL = dioidMonoL
  otimesMonoR = dioidMonoR

-- There is NO `IsAnnihilating HWMGrade`: hwmZero is also the sequence unit,
-- so  hwmSeq hwmZero a = a, not hwmZero.
-- tests/reject/HWMAnnihilates.idr is the negative control.
