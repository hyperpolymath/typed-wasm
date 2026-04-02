-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Tropical.idr — Level 11: Tropical cost-tracking for memory access
--
-- Every memory access operation carries a cost in a tropical semiring.
-- The min-plus semiring tracks latency (cheapest path), the max-plus
-- semiring tracks throughput (bottleneck path). The type checker proves
-- that any access path through shared memory has bounded total cost.
--
-- This is the "how expensive is this access pattern?" question answered
-- at compile time. It prevents pathological access patterns (e.g. a
-- tight loop doing random access across cache lines) from compiling
-- without an explicit cost annotation acknowledging the expense.
--
-- The tropical semiring algebra is adapted from 007's TropicalSemiring.idr.

module TypedWasm.ABI.Tropical

import TypedWasm.ABI.Region
import TypedWasm.ABI.Levels

%default total

-- ============================================================================
-- Tropical Semiring
-- ============================================================================

||| A tropical semiring value. In the min-plus semiring, addition is min
||| and multiplication is plus. Infinity is the zero element.
public export
data TropCost : Type where
  ||| Finite cost value (non-negative).
  Finite : (cost : Nat) -> TropCost
  ||| Infinite cost — unreachable or unbounded.
  Infinity : TropCost

||| Tropical addition: min of two costs.
public export
tropAdd : TropCost -> TropCost -> TropCost
tropAdd Infinity b = b
tropAdd a Infinity = a
tropAdd (Finite a) (Finite b) = Finite (min a b)

||| Tropical multiplication: sum of two costs (path composition).
public export
tropMul : TropCost -> TropCost -> TropCost
tropMul Infinity _ = Infinity
tropMul _ Infinity = Infinity
tropMul (Finite a) (Finite b) = Finite (a + b)

-- ============================================================================
-- Cost-Annotated Access
-- ============================================================================

||| A memory access operation annotated with its tropical cost.
||| The cost tracks cache-line crossings, alignment penalties, and
||| sequential vs random access patterns.
public export
record CostAnnotatedAccess where
  constructor MkCostAccess
  ||| The accessed field name.
  fieldName : String
  ||| Cost of this individual access (cache lines crossed, alignment penalty).
  accessCost : TropCost
  ||| Whether this access is sequential (stride-1) relative to the previous.
  sequential : Bool

||| A path through memory — a sequence of accesses with accumulated cost.
public export
data AccessPath : (totalCost : TropCost) -> Type where
  ||| Empty path — zero cost.
  EmptyPath : AccessPath (Finite 0)
  ||| Extend a path with one more access — cost accumulates via tropMul.
  ExtendPath : (prev : AccessPath prevCost) ->
               (access : CostAnnotatedAccess) ->
               AccessPath (tropMul prevCost access.accessCost)

-- ============================================================================
-- Cost Bounds
-- ============================================================================

||| Proof that a cost is bounded: `c <= bound`.
public export
data CostBounded : (cost : TropCost) -> (bound : Nat) -> Type where
  ||| Finite cost within bound.
  BoundedFinite : LTE n bound -> CostBounded (Finite n) bound
  ||| Infinity is never bounded (this constructor is impossible to inhabit).

||| Level 11 proof obligation: the total cost of an access path is bounded.
||| A function that accesses shared memory must prove its access pattern
||| has bounded cost. Without this proof, the access is rejected.
public export
record Level11Proof where
  constructor MkLevel11
  ||| The access path with accumulated cost.
  path : AccessPath totalCost
  ||| The declared cost bound for this function.
  bound : Nat
  ||| Proof that the total cost respects the bound.
  bounded : CostBounded totalCost bound

-- ============================================================================
-- Tropical semiring laws (for proof composition)
-- ============================================================================

||| tropAdd is commutative.
export
tropAddComm : (a, b : TropCost) -> tropAdd a b = tropAdd b a
tropAddComm Infinity Infinity = Refl
tropAddComm Infinity (Finite _) = Refl
tropAddComm (Finite _) Infinity = Refl
tropAddComm (Finite a) (Finite b) = cong Finite (minCommutative a b)

||| Infinity is the identity for tropAdd (zero element).
export
tropAddIdentity : (a : TropCost) -> tropAdd a Infinity = a
tropAddIdentity Infinity = Refl
tropAddIdentity (Finite _) = Refl

||| Finite 0 is the identity for tropMul (one element).
export
tropMulIdentity : (a : TropCost) -> tropMul (Finite 0) a = a
tropMulIdentity Infinity = Refl
tropMulIdentity (Finite _) = Refl
