-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra/Separation.idr — why the three grades must stay three.
--
-- Computed witnesses that the instances are not interchangeable.  Each is
-- `Refl` plus a decidable inequality on ℕ, so each is TESTED by the
-- typechecker's evaluator, not argued in prose:
--   S-1  an occupancy bound is not a cost bound          (HWM vs MaxPlus)
--   S-2  echo alternatives are MIN, tropical alternatives MAX (Loss vs MaxPlus)
--   S-3  the ⊕-induced order runs opposite ways in Loss and MaxPlus
--
-- Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Separation.agda @ cf9235c532712a783a404c359a1055f40134794a
-- Correspondence status: ASSUMED (transcription).
--
-- These are the reason typed-wasm does not fold its grades into one: L11's
-- cost (MaxPlus / the Loss carrier), L12's staleness (Loss) and L13's
-- occupancy (HWM) answer different questions.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra.Separation

import Data.Nat
import TypedWasm.ABI.ResourceAlgebra
import TypedWasm.ABI.ResourceAlgebra.Loss
import TypedWasm.ABI.ResourceAlgebra.MaxPlus
import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

-- ============================================================================
-- S-1  Sequencing peaks 2 and 3 (nothing held between them):
--      occupancy gives 3, cost gives 5.
-- ============================================================================

public export
two : HWMGrade
two = MkHWM 2 0 LTEZero

public export
three : HWMGrade
three = MkHWM 3 0 LTEZero

public export
hwmSeqPeak : peak (hwmSeq Separation.two Separation.three) = 3
hwmSeqPeak = Refl

public export
maxPlusSeqCost : maxPlusSeq (Val 2) (Val 3) = Val 5
maxPlusSeqCost = Refl

public export
threeNotFive : Not (the Nat 3 = 5)
threeNotFive Refl impossible

||| Agda `occupancy-is-not-cost`.
public export
occupancyIsNotCost : Not (peak (hwmSeq Separation.two Separation.three) = 5)
occupancyIsNotCost = threeNotFive

-- ============================================================================
-- S-2  Alternatives: echo picks the less lossy branch (min), tropical the
--      most expensive (max).  Same numbers, different grade.
-- ============================================================================

public export
lossAltPicksMin : lossAlt (Finite 2) (Finite 3) = Finite 2
lossAltPicksMin = Refl

public export
maxPlusAltPicksMax : maxPlusAlt (Val 2) (Val 3) = Val 3
maxPlusAltPicksMax = Refl

public export
twoNotThree : Not (the Nat 2 = 3)
twoNotThree Refl impossible

||| Agda `alternatives-differ`.
public export
alternativesDiffer : Not (lossAlt (Finite 2) (Finite 3) = Finite 3)
alternativesDiffer p = twoNotThree (finiteInjective p)

-- ============================================================================
-- S-3  The induced order: in MaxPlus 1 is below 2; in Loss 2 is below 1
--      (the numerically smaller loss is the one that absorbs).
-- ============================================================================

||| Agda `maxplus-order`.
public export
maxPlusOrder : LeG (Val 1) (Val 2)
maxPlusOrder = Refl

||| Agda `loss-order-reversed`.
public export
lossOrderReversed : LeG (Finite 2) (Finite 1)
lossOrderReversed = Refl
