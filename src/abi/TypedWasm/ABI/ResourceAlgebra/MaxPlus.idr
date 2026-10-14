-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra/MaxPlus.idr — the worst-case cost grade: max-plus on ℕ ∪ {−∞}.
--
-- THE ONE DEFINITION OF MAX-PLUS IN THIS TREE (tools/check-grade-kernel.sh).
--
-- Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Instances/MaxPlus.agda @ 0b338c9fc45cd04e7ee7d00b3855cd59d56a2afe
-- (unchanged since cf9235c, the pin it was first transcribed at)
-- which is itself the tropical-types grade (TropicalSessionTypes.lean).
-- Correspondence status: ASSUMED (transcription); operation table TESTED on
-- both sides by tests/transcription.  The Lean bridge (resource-algebra M-2)
-- stays OPEN: nothing mechanical links Lean, Agda and this module.
--
-- Renaming: constructors val / bot are Val / Bot; tAdd / tMul are
-- maxPlusAlt / maxPlusSeq.  Clause order is kept.
--
--   Grade = ℕ ∪ {−∞};  Bot = −∞
--   maxPlusAlt = max with Bot as identity   — alternatives, the "⊕"
--   maxPlusSeq = + with Bot absorbing       — sequence, the "⊗", unit Val 0
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra.MaxPlus

-- Re-exported so a consumer can REDUCE these grades at type level (the
-- definitions below unfold to Data.Nat's minimum / maximum and +).
import public Data.Nat
import TypedWasm.ABI.ResourceAlgebra
import TypedWasm.ABI.ResourceAlgebra.Nat

%default total

||| ℕ ∪ {−∞}.  Agda `Tropical` (val / bot).
public export
data MaxPlusGrade : Type where
  ||| A finite cost (Agda `val`).
  Val : (n : Nat) -> MaxPlusGrade
  ||| −∞: no run (Agda `bot`).
  Bot : MaxPlusGrade

||| Alternatives: the more expensive branch.  Agda `tAdd`.
public export
maxPlusAlt : MaxPlusGrade -> MaxPlusGrade -> MaxPlusGrade
maxPlusAlt Bot     b       = b
maxPlusAlt (Val m) Bot     = Val m
maxPlusAlt (Val m) (Val n) = Val (maximum m n)

||| Sequence: costs add.  Agda `tMul`.
public export
maxPlusSeq : MaxPlusGrade -> MaxPlusGrade -> MaxPlusGrade
maxPlusSeq Bot     _       = Bot
maxPlusSeq (Val m) Bot     = Bot
maxPlusSeq (Val m) (Val n) = Val (m + n)

||| `Val` is injective.
public export
valInjective : {m, n : Nat} -> Val m = Val n -> m = n
valInjective Refl = Refl

-- ============================================================================
-- Alternatives: (maxPlusAlt, Bot) is an idempotent commutative monoid
-- ============================================================================

||| Agda `tAdd-assoc`.
public export
maxPlusAltAssoc : (a, b, c : MaxPlusGrade) ->
                  maxPlusAlt (maxPlusAlt a b) c = maxPlusAlt a (maxPlusAlt b c)
maxPlusAltAssoc (Val a) (Val b) (Val c) = cong Val (maxAssoc a b c)
maxPlusAltAssoc (Val a) (Val b) Bot     = Refl
maxPlusAltAssoc (Val a) Bot     c       = Refl
maxPlusAltAssoc Bot     b       c       = Refl

||| Agda `tAdd-comm`.
public export
maxPlusAltComm : (a, b : MaxPlusGrade) -> maxPlusAlt a b = maxPlusAlt b a
maxPlusAltComm (Val a) (Val b) = cong Val (maximumCommutative a b)
maxPlusAltComm (Val a) Bot     = Refl
maxPlusAltComm Bot     (Val b) = Refl
maxPlusAltComm Bot     Bot     = Refl

||| Agda `tAdd-idem`.
public export
maxPlusAltIdem : (a : MaxPlusGrade) -> maxPlusAlt a a = a
maxPlusAltIdem (Val a) = cong Val (maximumIdempotent a)
maxPlusAltIdem Bot     = Refl

-- ============================================================================
-- Sequence: (maxPlusSeq, Val 0) is a monoid
-- ============================================================================

||| Agda `tMul-assoc`.
public export
maxPlusSeqAssoc : (a, b, c : MaxPlusGrade) ->
                  maxPlusSeq (maxPlusSeq a b) c = maxPlusSeq a (maxPlusSeq b c)
maxPlusSeqAssoc (Val a) (Val b) (Val c) = cong Val (plusAssoc a b c)
maxPlusSeqAssoc (Val a) (Val b) Bot     = Refl
maxPlusSeqAssoc (Val a) Bot     c       = Refl
maxPlusSeqAssoc Bot     b       c       = Refl

||| Agda `tMul-unitˡ`.
public export
maxPlusSeqUnitL : (a : MaxPlusGrade) -> maxPlusSeq (Val 0) a = a
maxPlusSeqUnitL (Val a) = Refl
maxPlusSeqUnitL Bot     = Refl

||| Agda `tMul-unitʳ`.
public export
maxPlusSeqUnitR : (a : MaxPlusGrade) -> maxPlusSeq a (Val 0) = a
maxPlusSeqUnitR (Val a) = cong Val (plusZeroRightNeutral a)
maxPlusSeqUnitR Bot     = Refl

-- ============================================================================
-- The instance, and its layers
-- ============================================================================

||| Agda `MaxPlus : ResourceAlgebra`.
public export
ResourceAlgebra MaxPlusGrade where
  oplus    = maxPlusAlt
  otimes   = maxPlusSeq
  zeroG    = Bot
  oneG     = Val 0
  altAssoc = maxPlusAltAssoc
  altComm  = maxPlusAltComm
  altIdem  = maxPlusAltIdem
  altUnitL = \_ => Refl
  seqAssoc = maxPlusSeqAssoc
  seqUnitL = maxPlusSeqUnitL
  seqUnitR = maxPlusSeqUnitR

||| Agda `MaxPlus-dioid` (distribˡ).
public export
maxPlusDistribL : (a, b, c : MaxPlusGrade) ->
                  maxPlusSeq a (maxPlusAlt b c)
                = maxPlusAlt (maxPlusSeq a b) (maxPlusSeq a c)
maxPlusDistribL (Val a) (Val b) (Val c) = cong Val (plusDistribLMax a b c)
maxPlusDistribL (Val a) (Val b) Bot     = Refl
maxPlusDistribL (Val a) Bot     (Val c) = Refl
maxPlusDistribL (Val a) Bot     Bot     = Refl
maxPlusDistribL Bot     b       c       = Refl

||| Agda `MaxPlus-dioid` (distribʳ).
public export
maxPlusDistribR : (a, b, c : MaxPlusGrade) ->
                  maxPlusSeq (maxPlusAlt a b) c
                = maxPlusAlt (maxPlusSeq a c) (maxPlusSeq b c)
maxPlusDistribR (Val a) (Val b) (Val c) = cong Val (plusDistribRMax a b c)
maxPlusDistribR (Val a) (Val b) Bot     = Refl
maxPlusDistribR (Val a) Bot     (Val c) = Refl
maxPlusDistribR (Val a) Bot     Bot     = Refl
maxPlusDistribR Bot     (Val b) (Val c) = Refl
maxPlusDistribR Bot     (Val b) Bot     = Refl
maxPlusDistribR Bot     Bot     c       = Refl

||| Agda `MaxPlus-dioid`.
public export
IsDioid MaxPlusGrade where
  distribL = maxPlusDistribL
  distribR = maxPlusDistribR

||| Agda `MaxPlus-ordered = IsDioid.ordered MaxPlus-dioid`.
public export
IsOrdered MaxPlusGrade where
  otimesMonoL = dioidMonoL
  otimesMonoR = dioidMonoR

||| Agda `MaxPlus-annihilating` (annihilʳ).
public export
maxPlusAnnihilR : (a : MaxPlusGrade) -> maxPlusSeq a Bot = Bot
maxPlusAnnihilR (Val _) = Refl
maxPlusAnnihilR Bot     = Refl

||| Agda `MaxPlus-annihilating`.
public export
IsAnnihilating MaxPlusGrade where
  annihilL = \_ => Refl
  annihilR = maxPlusAnnihilR

-- ============================================================================
-- typed-wasm additions (NOT in the Agda source): the order, read in ℕ
-- ============================================================================
--
-- The MaxPlus order IS ℕ's on finite grades:  Val m ≼ Val n  iff  m ≤ n.
-- L11's worst-case bound uses it to read a numeric bound as the kernel order.

||| m ≤ n gives Val m ≼ Val n.
public export
maxPlusLeOfLTE : {m, n : Nat} -> LTE m n -> LeG (Val m) (Val n)
maxPlusLeOfLTE le = cong Val (maximumOfLTE le)

||| Val m ≼ Val n gives m ≤ n.
public export
lteOfMaxPlusLe : (m, n : Nat) -> LeG (Val m) (Val n) -> LTE m n
lteOfMaxPlusLe m n prf = lteOfMaximum m n (valInjective prf)
