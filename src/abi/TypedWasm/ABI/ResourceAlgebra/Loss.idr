-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra/Loss.idr — the loss grade: min-plus on ℕ ∪ {∞}.
--
-- THE ONE DEFINITION OF MIN-PLUS IN THIS TREE (tools/check-grade-kernel.sh).
-- TypedWasm.ABI.Tropical's latency cost (TropCost) and TypedWasm.ABI.Echo's
-- loss grade are this carrier, not copies of it.
--
-- Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Instances/Loss.agda @ cf9235c532712a783a404c359a1055f40134794a
-- which is itself the echo-types loss grade
--   (echo-types experimental/echo-additive/Grade.agda).
-- Correspondence status: ASSUMED (transcription); operation table TESTED on
-- both sides by tests/transcription.
--
-- Renaming (the only change from the Agda text): constructors fin / inf are
-- Finite / Infinity, the names typed-wasm's L11/L12 code already uses;
-- _⊓g_ / _+g_ are lossAlt / lossSeq.  Clause order is kept, so the two
-- definitions reduce the same way on the same arguments.
--
--   Grade = ℕ ∪ {∞};  Finite 0 = no loss (echo `keep`);  Infinity = total collapse.
--   lossSeq = sequence (loss accumulates, ∞ absorbs)       — the "⊗"
--   lossAlt = alternatives = MIN (the less lossy option)  — the "⊕"
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra.Loss

-- Re-exported so a consumer can REDUCE these grades at type level (the
-- definitions below unfold to Data.Nat's minimum / maximum and +).
import public Data.Nat
import TypedWasm.ABI.ResourceAlgebra
import TypedWasm.ABI.ResourceAlgebra.Nat

%default total

||| ℕ ∪ {∞}.  Agda `Grade` (fin / inf).
public export
data LossGrade : Type where
  ||| A finite loss (Agda `fin`).
  Finite   : (n : Nat) -> LossGrade
  ||| Total collapse / unreachable (Agda `inf`).
  Infinity : LossGrade

||| Sequence: loss accumulates.  Agda `_+g_`.
public export
lossSeq : LossGrade -> LossGrade -> LossGrade
lossSeq (Finite m) (Finite n) = Finite (m + n)
lossSeq (Finite _) Infinity   = Infinity
lossSeq Infinity   _          = Infinity

||| Alternatives: the less lossy option.  Agda `_⊓g_`.
public export
lossAlt : LossGrade -> LossGrade -> LossGrade
lossAlt (Finite m) (Finite n) = Finite (minimum m n)
lossAlt (Finite m) Infinity   = Finite m
lossAlt Infinity   g          = g

||| `Finite` is injective.
public export
finiteInjective : {m, n : Nat} -> Finite m = Finite n -> m = n
finiteInjective Refl = Refl

-- ============================================================================
-- Alternatives: (lossAlt, Infinity) is an idempotent commutative monoid
-- ============================================================================

||| Agda `⊓g-assoc`.
public export
lossAltAssoc : (a, b, c : LossGrade) ->
               lossAlt (lossAlt a b) c = lossAlt a (lossAlt b c)
lossAltAssoc (Finite a) (Finite b) (Finite c) = cong Finite (minAssoc a b c)
lossAltAssoc (Finite a) (Finite b) Infinity   = Refl
lossAltAssoc (Finite a) Infinity   c          = Refl
lossAltAssoc Infinity   b          c          = Refl

||| Agda `⊓g-comm`.
public export
lossAltComm : (a, b : LossGrade) -> lossAlt a b = lossAlt b a
lossAltComm (Finite a) (Finite b) = cong Finite (minimumCommutative a b)
lossAltComm (Finite a) Infinity   = Refl
lossAltComm Infinity   (Finite b) = Refl
lossAltComm Infinity   Infinity   = Refl

||| Agda `⊓g-idem`.
public export
lossAltIdem : (a : LossGrade) -> lossAlt a a = a
lossAltIdem (Finite a) = cong Finite (minimumIdempotent a)
lossAltIdem Infinity   = Refl

-- ============================================================================
-- Sequence: (lossSeq, Finite 0) is a monoid
-- ============================================================================

||| Agda `+g-assoc`.
public export
lossSeqAssoc : (a, b, c : LossGrade) ->
               lossSeq (lossSeq a b) c = lossSeq a (lossSeq b c)
lossSeqAssoc (Finite a) (Finite b) (Finite c) = cong Finite (plusAssoc a b c)
lossSeqAssoc (Finite a) (Finite b) Infinity   = Refl
lossSeqAssoc (Finite a) Infinity   c          = Refl
lossSeqAssoc Infinity   b          c          = Refl

||| Agda `+g-unitˡ`.
public export
lossSeqUnitL : (a : LossGrade) -> lossSeq (Finite 0) a = a
lossSeqUnitL (Finite a) = Refl
lossSeqUnitL Infinity   = Refl

||| Agda `+g-unitʳ`.
public export
lossSeqUnitR : (a : LossGrade) -> lossSeq a (Finite 0) = a
lossSeqUnitR (Finite a) = cong Finite (plusZeroRightNeutral a)
lossSeqUnitR Infinity   = Refl

-- ============================================================================
-- The instance, and its layers
-- ============================================================================

||| Agda `Loss : ResourceAlgebra`.
public export
ResourceAlgebra LossGrade where
  oplus    = lossAlt
  otimes   = lossSeq
  zeroG    = Infinity
  oneG     = Finite 0
  altAssoc = lossAltAssoc
  altComm  = lossAltComm
  altIdem  = lossAltIdem
  altUnitL = \_ => Refl
  seqAssoc = lossSeqAssoc
  seqUnitL = lossSeqUnitL
  seqUnitR = lossSeqUnitR

||| Agda `Loss-dioid` (distribˡ).
public export
lossDistribL : (a, b, c : LossGrade) ->
               lossSeq a (lossAlt b c) = lossAlt (lossSeq a b) (lossSeq a c)
lossDistribL (Finite a) (Finite b) (Finite c) = cong Finite (plusDistribLMin a b c)
lossDistribL (Finite a) (Finite b) Infinity   = Refl
lossDistribL (Finite a) Infinity   c          = Refl
lossDistribL Infinity   b          c          = Refl

||| Agda `Loss-dioid` (distribʳ).
public export
lossDistribR : (a, b, c : LossGrade) ->
               lossSeq (lossAlt a b) c = lossAlt (lossSeq a c) (lossSeq b c)
lossDistribR (Finite a) (Finite b) (Finite c) = cong Finite (plusDistribRMin a b c)
lossDistribR (Finite a) (Finite b) Infinity   = Refl
lossDistribR (Finite a) Infinity   (Finite c) = Refl
lossDistribR (Finite a) Infinity   Infinity   = Refl
lossDistribR Infinity   b          c          = Refl

||| Agda `Loss-dioid`.
public export
IsDioid LossGrade where
  distribL = lossDistribL
  distribR = lossDistribR

||| Agda `Loss-ordered = IsDioid.ordered Loss-dioid`.
public export
IsOrdered LossGrade where
  otimesMonoL = dioidMonoL
  otimesMonoR = dioidMonoR

||| Agda `Loss-annihilating` (annihilʳ).
public export
lossAnnihilR : (a : LossGrade) -> lossSeq a Infinity = Infinity
lossAnnihilR (Finite _) = Refl
lossAnnihilR Infinity   = Refl

||| Agda `Loss-annihilating`.
public export
IsAnnihilating LossGrade where
  annihilL = \_ => Refl
  annihilR = lossAnnihilR

-- ============================================================================
-- typed-wasm additions (NOT in the Agda source): the order, read in ℕ
-- ============================================================================
--
-- Separation S-3 says the Loss order runs opposite to ℕ's.  Precisely:
--   Finite n ≼ Finite k   iff   k ≤ n,
-- and Infinity (𝟘) is below everything, Finite 0 (𝟙) above everything.
-- L11 uses this to read a numeric cost bound as the kernel order.

||| `Finite` is never `Infinity`.
public export
finiteNotInfinity : {n : Nat} -> Not (Finite n = Infinity)
finiteNotInfinity Refl impossible

||| k ≤ n gives Finite n ≼ Finite k.
public export
lossLeOfLTE : {k, n : Nat} -> LTE k n -> LeG (Finite n) (Finite k)
lossLeOfLTE le = cong Finite (minimumOfLTE le)

||| Finite n ≼ Finite k gives k ≤ n.
public export
lteOfLossLe : (n, k : Nat) -> LeG (Finite n) (Finite k) -> LTE k n
lteOfLossLe n k prf = lteOfMinimum n k (finiteInjective prf)

||| Infinity is the least grade, so no finite grade sits below it:
||| Finite n ≼ Infinity is false.
public export
finiteNotLeInfinity : {n : Nat} -> Not (LeG (Finite n) Infinity)
finiteNotLeInfinity prf = finiteNotInfinity prf

||| 𝟙 (= Finite 0, no loss) is the top of the Loss order.
public export
lossLeOne : (g : LossGrade) -> LeG g (Finite 0)
lossLeOne (Finite n) = cong Finite (minimumZeroZeroLeft n)
lossLeOne Infinity   = Refl
