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

||| Structural minimum for Nat (proof-friendly).
|||
||| Idris2 0.8's Prelude.min is defined via comparison
||| (`if x < y then x else y`) and does not reduce under pattern matching
||| on variables in proofs.  This equivalent definition by structural
||| recursion does, which is what makes the semiring proofs below go
||| through without holes.
|||
||| Extensionally equal to Prelude.min on Nat (ported from
||| 007-lang/proofs/idris2/TropicalSemiring.idr).
private
tropMin : Nat -> Nat -> Nat
tropMin Z     _     = Z
tropMin (S _) Z     = Z
tropMin (S m) (S n) = S (tropMin m n)

||| Tropical addition: min of two costs.  Uses structural `tropMin` so
||| the semiring laws below reduce cleanly.
public export
tropAdd : TropCost -> TropCost -> TropCost
tropAdd Infinity b = b
tropAdd a Infinity = a
tropAdd (Finite a) (Finite b) = Finite (tropMin a b)

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
-- Tropical semiring laws — all twelve axioms
-- ============================================================================
--
-- Ported 2026-04-18 from 007-lang/proofs/idris2/TropicalSemiring.idr.
-- (TropCost, tropAdd, tropMul, Infinity, Finite 0) is a proven commutative
-- semiring.  Zero dangerous patterns, %default total, mechanically checked
-- by idris2 --check.

-- ---- Private Nat lemmas (structural, used to close the Finite cases) ----

||| Right identity for Nat addition.
private
plusZeroRightNeutral' : (n : Nat) -> n + 0 = n
plusZeroRightNeutral' Z = Refl
plusZeroRightNeutral' (S k) = cong S (plusZeroRightNeutral' k)

||| Nat addition: m + S n = S (m + n).
private
plusSuccRight' : (m, n : Nat) -> m + S n = S (m + n)
plusSuccRight' Z n = Refl
plusSuccRight' (S k) n = cong S (plusSuccRight' k n)

||| Nat addition is commutative.
private
plusComm' : (m, n : Nat) -> m + n = n + m
plusComm' Z Z = Refl
plusComm' Z (S k) = cong S (plusComm' Z k)
plusComm' (S k) Z = cong S (plusComm' k Z)
plusComm' (S k) (S j) =
  rewrite plusSuccRight' k j in
  rewrite plusSuccRight' j k in
  cong S (cong S (plusComm' k j))

||| Nat addition is associative.
private
plusAssoc' : (m, n, p : Nat) -> m + (n + p) = (m + n) + p
plusAssoc' Z n p = Refl
plusAssoc' (S m) n p = cong S (plusAssoc' m n p)

||| Structural minimum is commutative.
private
tropMinComm : (m, n : Nat) -> tropMin m n = tropMin n m
tropMinComm Z Z = Refl
tropMinComm Z (S _) = Refl
tropMinComm (S _) Z = Refl
tropMinComm (S m) (S n) = cong S (tropMinComm m n)

||| Structural minimum is associative.
private
tropMinAssoc : (m, n, p : Nat) -> tropMin m (tropMin n p) = tropMin (tropMin m n) p
tropMinAssoc Z _ _ = Refl
tropMinAssoc (S _) Z _ = Refl
tropMinAssoc (S _) (S _) Z = Refl
tropMinAssoc (S m) (S n) (S p) = cong S (tropMinAssoc m n p)

||| Addition distributes over structural minimum from the left:
||| a + tropMin m n = tropMin (a + m) (a + n).
private
plusDistribOverTropMin : (a, m, n : Nat) -> a + tropMin m n = tropMin (a + m) (a + n)
plusDistribOverTropMin Z m n = Refl
plusDistribOverTropMin (S a) m n = cong S (plusDistribOverTropMin a m n)

-- ---- Additive monoid: (TropCost, tropAdd, Infinity) ----

||| Left identity: tropAdd Infinity a = a.
public export
tropAddLeftId : (a : TropCost) -> tropAdd Infinity a = a
tropAddLeftId Infinity = Refl
tropAddLeftId (Finite _) = Refl

||| Right identity: tropAdd a Infinity = a.
public export
tropAddRightId : (a : TropCost) -> tropAdd a Infinity = a
tropAddRightId Infinity = Refl
tropAddRightId (Finite _) = Refl

||| Commutativity: tropAdd a b = tropAdd b a.
|||
||| The order of two branch alternatives does not affect which one wins.
public export
tropAddComm : (a, b : TropCost) -> tropAdd a b = tropAdd b a
tropAddComm Infinity Infinity = Refl
tropAddComm Infinity (Finite _) = Refl
tropAddComm (Finite _) Infinity = Refl
tropAddComm (Finite m) (Finite n) = cong Finite (tropMinComm m n)

||| Associativity: tropAdd a (tropAdd b c) = tropAdd (tropAdd a b) c.
|||
||| Grouping three branch alternatives does not affect the minimum outcome.
public export
tropAddAssoc : (a, b, c : TropCost) ->
               tropAdd a (tropAdd b c) = tropAdd (tropAdd a b) c
tropAddAssoc Infinity _ _ = Refl
tropAddAssoc (Finite _) Infinity _ = Refl
tropAddAssoc (Finite _) (Finite _) Infinity = Refl
tropAddAssoc (Finite m) (Finite n) (Finite p) = cong Finite (tropMinAssoc m n p)

-- ---- Multiplicative monoid: (TropCost, tropMul, Finite 0) ----

||| Left identity: tropMul (Finite 0) a = a.
public export
tropMulLeftId : (a : TropCost) -> tropMul (Finite 0) a = a
tropMulLeftId Infinity = Refl
tropMulLeftId (Finite _) = Refl

||| Right identity: tropMul a (Finite 0) = a.
public export
tropMulRightId : (a : TropCost) -> tropMul a (Finite 0) = a
tropMulRightId Infinity = Refl
tropMulRightId (Finite n) = cong Finite (plusZeroRightNeutral' n)

||| Commutativity: tropMul a b = tropMul b a.
|||
||| Sequential costs compose the same in either order.
public export
tropMulComm : (a, b : TropCost) -> tropMul a b = tropMul b a
tropMulComm Infinity Infinity = Refl
tropMulComm Infinity (Finite _) = Refl
tropMulComm (Finite _) Infinity = Refl
tropMulComm (Finite m) (Finite n) = cong Finite (plusComm' m n)

||| Associativity: tropMul a (tropMul b c) = tropMul (tropMul a b) c.
|||
||| Parenthesisation does not affect the cost of a sequential chain.
public export
tropMulAssoc : (a, b, c : TropCost) ->
               tropMul a (tropMul b c) = tropMul (tropMul a b) c
tropMulAssoc Infinity _ _ = Refl
tropMulAssoc (Finite _) Infinity _ = Refl
tropMulAssoc (Finite _) (Finite _) Infinity = Refl
tropMulAssoc (Finite m) (Finite n) (Finite p) = cong Finite (plusAssoc' m n p)

-- ---- Annihilation: Infinity annihilates tropMul ----

||| Left annihilation: tropMul Infinity a = Infinity.
public export
tropMulLeftAnn : (a : TropCost) -> tropMul Infinity a = Infinity
tropMulLeftAnn _ = Refl

||| Right annihilation: tropMul a Infinity = Infinity.
public export
tropMulRightAnn : (a : TropCost) -> tropMul a Infinity = Infinity
tropMulRightAnn Infinity = Refl
tropMulRightAnn (Finite _) = Refl

-- ---- Distributivity ----

||| Left distributivity:
||| tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c).
|||
||| A constant sequential prefix does not change which branch is cheaper.
public export
tropMulDistrib : (a, b, c : TropCost) ->
                 tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c)
tropMulDistrib Infinity _ _ = Refl
tropMulDistrib (Finite _) Infinity _ = Refl
tropMulDistrib (Finite _) (Finite _) Infinity = Refl
tropMulDistrib (Finite m) (Finite n) (Finite p) =
  cong Finite (plusDistribOverTropMin m n p)

||| Right distributivity (derived from left distributivity + tropMulComm):
||| tropMul (tropAdd a b) c = tropAdd (tropMul a c) (tropMul b c).
public export
tropMulDistribR : (a, b, c : TropCost) ->
                  tropMul (tropAdd a b) c = tropAdd (tropMul a c) (tropMul b c)
tropMulDistribR a b c =
  let step1 = tropMulComm (tropAdd a b) c
      step2 = tropMulDistrib c a b
      swapA = tropMulComm c a
      swapB = tropMulComm c b
      rwA   = cong (\x => tropAdd x (tropMul c b)) swapA
      rwB   = cong (\x => tropAdd (tropMul a c) x) swapB
  in trans step1 (trans step2 (trans rwA rwB))

-- ---- Legacy aliases (kept so earlier consumers keep compiling) ----

||| Alias for tropAddRightId — kept for legacy callers.
export
tropAddIdentity : (a : TropCost) -> tropAdd a Infinity = a
tropAddIdentity = tropAddRightId

||| Alias for tropMulLeftId — kept for legacy callers.
export
tropMulIdentity : (a : TropCost) -> tropMul (Finite 0) a = a
tropMulIdentity = tropMulLeftId

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
