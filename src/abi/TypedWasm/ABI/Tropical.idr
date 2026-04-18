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
import Data.Nat
import Data.Fin
import Data.List

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
  -- Infinity is never bounded: there is no constructor for that case, so
  -- `CostBounded Infinity _` is uninhabited by construction.

||| Level 11 proof obligation: the total cost of an access path is bounded.
||| A function that accesses shared memory must prove its access pattern
||| has bounded cost. Without this proof, the access is rejected.
public export
record Level11Proof where
  constructor MkLevel11
  ||| The accumulated cost along the path (existential).
  totalCost : TropCost
  ||| The access path with accumulated cost.
  path : AccessPath totalCost
  ||| The declared cost bound for this function.
  bound : Nat
  ||| Proof that the total cost respects the bound.
  bounded : CostBounded totalCost bound

-- ============================================================================
-- Tropical semiring laws (for proof composition)
-- ============================================================================

-- The full commutative-semiring proof (eight axioms including
-- commutativity, associativity, annihilation, distributivity) is deferred
-- to A2: port from 007-lang/proofs/idris2/TropicalSemiring.idr which uses
-- a structural `tropMin` because Prelude.min does not reduce under pattern
-- matching in Idris2 0.8.  See PROOF-NEEDS.md §P0.1.
--
-- The two identity theorems below go through directly because they do not
-- touch `min` on the Finite/Finite case.

||| Infinity is the right identity for tropAdd (zero element).
export
tropAddIdentity : (a : TropCost) -> tropAdd a Infinity = a
tropAddIdentity Infinity = Refl
tropAddIdentity (Finite _) = Refl

||| Finite 0 is the left identity for tropMul (one element).
export
tropMulIdentity : (a : TropCost) -> tropMul (Finite 0) a = a
tropMulIdentity Infinity = Refl
tropMulIdentity (Finite _) = Refl

-- ============================================================================
-- All-Pairs Cost Matrix (Kleene Star / Floyd-Warshall)
-- ============================================================================
--
-- The Kleene star of a cost matrix A gives, at entry (i,j), the minimum
-- accumulated cost to go from field i to field j via any sequence of accesses.
-- This is the all-pairs shortest-path matrix under the min-plus semiring.
--
-- Mathematical foundation: the Isabelle proofs in
-- hyperpolymath/tropical-resource-typing (commit f6c5a6f, 2026-04-11) establish
-- for the dual max-plus semiring:
--   - Star equation:      A* = I ⊕ A · A*    (Tropical_Kleene.thy)
--   - Least prefixpoint:  A* ≤ X for all X ≥ I ⊕ A · X  (Tropical_Kleene.thy)
--   - Floyd-Warshall:     (I ⊕ A)^{n-1} = A* (under no_pos_cycle)
--                                           (Tropical_Matrices_Clean.thy)
--   - Star idempotency:   (A*)* = A*          (Tropical_CNO.thy)
-- By duality (swap min↔max) these hold for the min-plus semiring here.
--
-- For typed-wasm, the access graph between fields is structurally acyclic
-- (no field transitively contains itself), so the no_pos_cycle condition
-- holds unconditionally.  Star = Floyd-Warshall closure = shortest-path matrix.

||| An n × n cost matrix: entry (i, j) is the direct access cost from field i
||| to field j.  Infinity means no direct access exists.
public export
CostMatrix : (n : Nat) -> Type
CostMatrix n = Fin n -> Fin n -> TropCost

||| Matrix addition (pointwise min).
public export
costMatAdd : CostMatrix n -> CostMatrix n -> CostMatrix n
costMatAdd m1 m2 i j = tropAdd (m1 i j) (m2 i j)

||| Matrix multiplication in the min-plus semiring.
||| (m1 · m2)(i,j) = min_k { m1(i,k) + m2(k,j) }.
public export
costMatMul : {n : Nat} -> CostMatrix n -> CostMatrix n -> CostMatrix n
costMatMul {n} m1 m2 i j = go (List.allFins n)
  where
    go : List (Fin n) -> TropCost
    go [] = Infinity
    go (k :: ks) = tropAdd (go ks) (tropMul (m1 i k) (m2 k j))

||| Identity cost matrix: 0 on the diagonal (free self-access), Infinity off.
public export
costMatId : {n : Nat} -> CostMatrix n
costMatId i j = if i == j then Finite 0 else Infinity

||| n-th power of a cost matrix.
public export
costMatPow : {n : Nat} -> CostMatrix n -> Nat -> CostMatrix n
costMatPow _  Z    = costMatId
costMatPow m (S k) = costMatMul m (costMatPow m k)

||| Kleene star of a cost matrix: A* = I ⊕ A ⊕ A² ⊕ … ⊕ A^{n-1}.
||| In the min-plus semiring this computes all-pairs shortest paths via
||| repeated matrix squaring (Floyd-Warshall style).
||| For an n-field access graph, n-1 steps suffice (no field visits itself twice
||| on a simple path).
public export
costMatStar : {n : Nat} -> CostMatrix n -> CostMatrix n
costMatStar {n = Z}   _ = costMatId
costMatStar {n = S m} a = go (List.allFins (S m))
  where
    go : List (Fin (S m)) -> CostMatrix (S m)
    go [] = costMatId
    go (k :: ks) = costMatAdd (go ks) (costMatPow a (finToNat k))

-- ============================================================================
-- All-Pairs Cost Proof
-- ============================================================================

||| Proof that entry (i, j) in a cost matrix is bounded.
public export
data EntryBounded : TropCost -> Nat -> Type where
  EntryFin : LTE n bound -> EntryBounded (Finite n) bound

||| The all-pairs cost matrix for a field layout, bundled with its bound proof.
||| Every entry (i,j) gives the minimum cost to access field j from field i,
||| and the total cost is provably bounded by `pathBound`.
public export
record AllPairsCosts (n : Nat) where
  constructor MkAllPairsCosts
  ||| The raw n × n cost matrix (direct access costs).
  directCosts : CostMatrix n
  ||| The star-closed cost matrix (all-pairs shortest paths).
  starCosts   : CostMatrix n
  ||| Declared per-path cost bound.
  pathBound   : Nat
  ||| Proof that every star-cost entry is bounded.
  bounded     : (i, j : Fin n) -> EntryBounded (starCosts i j) pathBound

||| Level 11 Kleene proof obligation: attach an AllPairsCosts to a function's
||| memory access pattern.  Replaces the single-path Level11Proof when the
||| function accesses multiple fields and needs a global cost certificate.
public export
record Level11KleeneProof (n : Nat) where
  constructor MkLevel11Kleene
  ||| The all-pairs cost structure for this function's field layout.
  costs      : AllPairsCosts n
  ||| The sequence of field indices accessed (as a list of Fin n).
  accessSeq  : List (Fin n)
  ||| The computed path cost along the access sequence.
  pathCost   : TropCost
  ||| Proof that the path cost respects the global bound.
  inBound    : EntryBounded pathCost (costs.pathBound)
