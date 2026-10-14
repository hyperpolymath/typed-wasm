-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Occupancy.idr — L13 occupancy: the high-water-mark grade of private memory
-- and what a module-isolation boundary reclaims.
--
-- L13 (ModuleIsolation.idr) proves ACCESS isolation.  This module adds the
-- OCCUPANCY reading: a private memory's run is graded in the kernel's HWM
-- instance (peak live state, drift still held at the end), and a declared
-- boundary is a cut in that run.  The reclamation law says what the cut
-- frees: the suffix after it starts from the prefix's DRIFT, not its PEAK,
-- so peak − drift is reclaimed at the boundary.
--
-- PROVENANCE.  Ported and re-proved from hyperpolymath/occupancy-types
--   src/OccupancyTypes/{Order,Timeline,Reclaim,Witness}.agda @ af957280075699c659de0abd9a3b0defade77309
-- (fetched by scripts/fetch-siblings.sh), which states them over
-- resource-algebra's Instances/HWM.agda, the source of
-- TypedWasm.ABI.ResourceAlgebra.HWM.  Agda is the proof kernel; these Idris2
-- proofs are the ABI layer's own.  Statement correspondence: ASSUMED
-- (port-and-reprove).  Map: Timeline (Agda data) -> List; grade -> timelineGrade;
-- cut-factor -> cutFactor (R-1); reclaim-law / occupancy-at-cut ->
-- reclaimLaw / occupancyAtCut (R-2); occupancy≤cost / protocol-occupancy≤cost
-- -> occupancyLeCost / protocolOccupancyLeCost (R-3); no-reclaim / reclaimed
-- -> noReclaim / reclaimed (R-4); Witness -> witness* (R-5); the R-6 rejects
-- are tests/reject/{CostIsOccupancy,DriftIsPeak}.idr.
--
-- WHAT IS DESIGNED, NOT PROVED.  That the HWM unit is a WebAssembly page of
-- the private memory, that a module's run is the sequence of its phases, and
-- that a declared L13 boundary is where the run is cut: no operational
-- semantics links the grade to `memory.grow` or to actual frees, and no
-- surface checker emits these grades.  `striated` regions are surface syntax
-- only (no ABI type), so their occupancy is OPEN.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.Occupancy

import Data.List
import Data.List.Elem
import Data.Nat

import TypedWasm.ABI.ResourceAlgebra
import public TypedWasm.ABI.ResourceAlgebra.HWM
import TypedWasm.ABI.ResourceAlgebra.MaxPlus
import TypedWasm.ABI.ModuleIsolation

%default total

-- ============================================================================
-- Order lemmas — occupancy-types Order.agda (beyond what base provides)
-- ============================================================================

||| Agda `<-+ʳ`: a positive summand makes the sum strictly bigger.
private
ltPlusPositive : (m : Nat) -> {n : Nat} -> LT 0 n -> LT m (m + n)
ltPlusPositive m {n = S k} _ =
  rewrite sym (plusSuccRightSucc m k) in LTESucc (lteAddRight m)

-- ============================================================================
-- R-1  A run as the sequence of its phases; the grade factors at every cut
--      (occupancy-types Timeline.agda, parametric in the algebra)
-- ============================================================================

||| The grade of a run: its phases in sequence.  Agda `Timeline.grade`.
public export
timelineGrade : ResourceAlgebra g => List g -> g
timelineGrade []        = oneG
timelineGrade (x :: xs) = otimes x (timelineGrade xs)

||| Cutting a run anywhere factors its grade, in any resource algebra.
||| Agda `cut-factor` (R-1).
public export
cutFactor : ResourceAlgebra g => (xs, ys : List g) ->
            timelineGrade (xs ++ ys) = otimes (timelineGrade xs) (timelineGrade ys)
cutFactor []        ys = sym (seqUnitL (timelineGrade ys))
cutFactor (x :: xs) ys =
  trans (cong (otimes x) (cutFactor xs ys))
        (sym (seqAssoc x (timelineGrade xs) (timelineGrade ys)))

-- ============================================================================
-- R-2 .. R-4  Reclamation at a cut — occupancy-types Reclaim.agda
-- ============================================================================

||| The reclamation law: the suffix sees the prefix's drift.  Agda
||| `reclaim-law` (R-2).
public export
reclaimLaw : (a, b : HWMGrade) ->
             peak (hwmSeq a b) = maximum (peak a) (drift a + peak b)
reclaimLaw (MkHWM _ _ _) (MkHWM _ _ _) = Refl

||| Occupancy never exceeds cost.  Agda `occupancy≤cost` (R-3).
public export
occupancyLeCost : (a, b : HWMGrade) -> LTE (peak (hwmSeq a b)) (peak a + peak b)
occupancyLeCost (MkHWM p1 n1 b1) (MkHWM p2 n2 b2) =
  maxLub (lteAddRight p1) (plusLteMonotoneRight p2 n1 p1 b1)

||| Nothing reclaimed (drift = peak): occupancy IS cost.  Agda `no-reclaim` (R-4).
public export
noReclaim : (a : HWMGrade) -> peak a = drift a -> (c : HWMGrade) ->
            peak (hwmSeq a c) = peak a + peak c
noReclaim (MkHWM p n b) eq (MkHWM p2 n2 b2) =
  rewrite sym eq in
  trans (maximumCommutative p (p + p2)) (maxAbsorbLTE (lteAddRight p))

||| Strict reclamation: something is released at the cut and the suffix does
||| something, so occupancy is strictly below cost.  Agda `reclaimed` (R-4).
public export
reclaimed : (a, c : HWMGrade) -> LT (drift a) (peak a) -> LT 0 (peak c) ->
            LT (peak (hwmSeq a c)) (peak a + peak c)
reclaimed (MkHWM p1 n1 b1) (MkHWM p2 n2 b2) lt pos =
  maxLub (ltPlusPositive p1 pos) (plusLteMonotoneRight p2 (S n1) p1 lt)

||| At the level of runs: the cut factorisation plus the law.  Agda
||| `occupancy-at-cut` (R-2).
public export
occupancyAtCut : (xs, ys : List HWMGrade) ->
                 peak (timelineGrade (xs ++ ys))
               = maximum (peak (timelineGrade xs))
                         (drift (timelineGrade xs) + peak (timelineGrade ys))
occupancyAtCut xs ys =
  trans (cong peak (cutFactor xs ys)) (reclaimLaw (timelineGrade xs) (timelineGrade ys))

||| Agda `protocol-occupancy≤cost` (R-3).
public export
protocolOccupancyLeCost : (xs, ys : List HWMGrade) ->
                          LTE (peak (timelineGrade (xs ++ ys)))
                              (peak (timelineGrade xs) + peak (timelineGrade ys))
protocolOccupancyLeCost xs ys =
  rewrite cutFactor xs ys in occupancyLeCost (timelineGrade xs) (timelineGrade ys)

-- ============================================================================
-- R-5  Two readings of one run — occupancy-types Witness.agda (computed)
-- ============================================================================
--
-- Phase 1 allocates 4 and releases 3 (drift 1); phase 2 allocates 3 and
-- holds it.  Occupancy 4 (3 reclaimed at the cut), cost 7.

public export
witnessA : HWMGrade
witnessA = MkHWM 4 1 (LTESucc LTEZero)

public export
witnessB : HWMGrade
witnessB = MkHWM 3 3 (LTESucc (LTESucc (LTESucc LTEZero)))

||| Agda `Witness.occupancy`.
public export
witnessOccupancy : peak (timelineGrade [Occupancy.witnessA, Occupancy.witnessB]) = 4
witnessOccupancy = Refl

||| Agda `Witness.cost`.
public export
witnessCost : timelineGrade [Val 4, Val 3] = Val 7
witnessCost = Refl

||| Agda `Witness.strict`.
public export
witnessStrict : LT (peak (hwmSeq Occupancy.witnessA Occupancy.witnessB))
                   (peak Occupancy.witnessA + peak Occupancy.witnessB)
witnessStrict =
  reclaimed witnessA witnessB (LTESucc (LTESucc LTEZero)) (LTESucc LTEZero)

-- ============================================================================
-- L13 binding — private memory and boundaries (DESIGNED; see header)
-- ============================================================================

||| What a cut reclaims: peak − drift.
public export
reclaimedAt : HWMGrade -> Nat
reclaimedAt g = minus (peak g) (drift g)

||| What is reclaimed and what is still held make up the peak exactly.
public export
reclaimedPlusDrift : (g : HWMGrade) -> reclaimedAt g + drift g = peak g
reclaimedPlusDrift (MkHWM p n b) = plusMinusLte n p b

||| A private memory's run stays within its declared maximum (in pages).
public export
data WithinMaximum : PrivateMemory -> HWMGrade -> Type where
  ||| No maximum declared.
  NoMaximum    : {pm : PrivateMemory} -> {g : HWMGrade} ->
                 pm.maximum = Nothing -> WithinMaximum pm g
  ||| The peak does not exceed the declared maximum.
  UnderMaximum : {pm : PrivateMemory} -> {g : HWMGrade} -> {m : Nat} ->
                 pm.maximum = Just m -> LTE (peak g) m -> WithinMaximum pm g

||| A private memory graded by occupancy: its run, phase by phase, and the
||| proof that the run's high-water mark fits the declaration.
public export
record OccupancyGradedMemory where
  constructor MkOccupancyGraded
  ||| The L13 private memory.
  memory : PrivateMemory
  ||| Its run, as consecutive phases.
  phases : List HWMGrade
  ||| The run's peak fits the declared maximum.
  fits   : WithinMaximum memory (timelineGrade phases)

||| A run of an isolated module, cut at one of its declared boundaries.
public export
record BoundaryCut (m : IsolatedModule) where
  constructor MkBoundaryCut
  ||| The boundary the run crosses.
  boundary : Boundary
  ||| It is one the module declared (L13 well-formedness applies to it).
  declared : Elem boundary m.boundaries
  ||| Phases before the boundary.
  before   : List HWMGrade
  ||| Phases after it.
  after    : List HWMGrade

||| What the boundary frees: the prefix's peak − drift.
public export
boundaryFrees : BoundaryCut m -> Nat
boundaryFrees c = reclaimedAt (timelineGrade c.before)

||| R-2 at an L13 boundary: the run after the boundary starts from what the
||| run before it still holds.
public export
boundaryOccupancy : (c : BoundaryCut m) ->
                    peak (timelineGrade (c.before ++ c.after))
                  = maximum (peak (timelineGrade c.before))
                            (drift (timelineGrade c.before) + peak (timelineGrade c.after))
boundaryOccupancy c = occupancyAtCut c.before c.after

||| R-3 at an L13 boundary: occupancy across a boundary never exceeds the
||| cost of the two sides.
public export
boundaryOccupancyLeCost : (c : BoundaryCut m) ->
                          LTE (peak (timelineGrade (c.before ++ c.after)))
                              (peak (timelineGrade c.before) + peak (timelineGrade c.after))
boundaryOccupancyLeCost c = protocolOccupancyLeCost c.before c.after

||| The budget rule a checker would apply at a boundary: if the run before
||| fits in `m`, and the run after fits in what the boundary left (m minus
||| the drift), the whole run fits in `m`.
public export
fitsAcrossBoundary : {m : Nat} -> (xs, ys : List HWMGrade) ->
                     LTE (peak (timelineGrade xs)) m ->
                     LTE (drift (timelineGrade xs) + peak (timelineGrade ys)) m ->
                     LTE (peak (timelineGrade (xs ++ ys))) m
fitsAcrossBoundary xs ys before after =
  rewrite occupancyAtCut xs ys in maxLub before after
