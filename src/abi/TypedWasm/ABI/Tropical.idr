-- SPDX-License-Identifier: MPL-2.0
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
--
-- ----------------------------------------------------------------------------
-- Estate cross-reference (audit 2026-06-16) — canonical axis: Lean4
-- hyperpolymath/tropical-resource-typing @ 2e35229.
--
-- This module's (TropCost, tropAdd = min, tropMul = +, Infinity, Finite 0) is
-- the Idris2 analogue of the canonical Resource.Instances.MinPlus instance,
-- and the twelve axioms below correspond to the canonical ResourceSemiring
-- fields.  It is a DELIBERATE Idris2 mirror, not a literal import: the
-- canonical repo is Lean4/Isabelle and there is no Lean->Idris proof-transport
-- path, so the algebra above is sourced from 007's TropicalSemiring.idr.
--
-- Mirrored:    min-plus semiring + Kleene/Floyd-Warshall all-pairs closure.
-- NOT yet mirrored (debt, tracked for owner decision):
--   * ResourceAlgebra/Ordered interface (the dioid order a |+| b = b),
--   * parametric_resource_transport (one-shot law transport to all instances),
--   * the MinMax / Bridge.hub_ceiling BOTTLENECK instance,
--   * the MaxPlus worst-case-budget instance,
--   * Resource.EchoBridge.ResidueMeasure (E -> R residue measure; would wire
--     the sibling TypedWasm.ABI.Echo into this grade).
-- typed-wasm holds one thing the canonical Lean axis lacks: the Kleene-closure
-- matrix layer below (extend-upstream candidate; owner sign-off required).
-- ----------------------------------------------------------------------------

module TypedWasm.ABI.Tropical

import TypedWasm.ABI.Region
import TypedWasm.ABI.Levels
import Data.Nat
import Data.Fin
import Data.List
import Data.List.Elem

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
-- hyperpolymath/tropical-resource-typing (commit 2e35229; the Kleene/matrix
-- math lives in the Isabelle .thy files below, while the consumer-facing axis
-- is now the Lean4 Resource.* interface — see the estate cross-reference at the
-- top of this file) establish for the dual max-plus semiring:
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

-- ============================================================================
-- Ordered layer — the canonical dioid order  (Resource.Algebra.Ordered)
-- ============================================================================
--
-- Mirrors hyperpolymath/tropical-resource-typing Resource/Algebra/Ordered.lean
-- @ 2e35229.  The canonical resource order is the dioid order
--   a |<=| b  :=  tropAdd a b = b      (canonical: a |+| b = b)
-- For this MinPlus instance |+| = min, so the order is the REVERSE of numeric
-- <=: Finite m |<=| Finite n  iff  n <= m, and Infinity (the additive zero /
-- +inf) is the LEAST element.  Smaller cost sits higher.

||| Structural minimum is idempotent.
private
tropMinIdem : (m : Nat) -> tropMin m m = m
tropMinIdem Z = Refl
tropMinIdem (S k) = cong S (tropMinIdem k)

||| The canonical dioid order: a refines b iff combining them is b.
public export
tropLe : TropCost -> TropCost -> Type
tropLe a b = tropAdd a b = b

||| TropCost addition is idempotent (the dioid property).
public export
tropAddIdem : (a : TropCost) -> tropAdd a a = a
tropAddIdem Infinity = Refl
tropAddIdem (Finite n) = cong Finite (tropMinIdem n)

||| |<=| is reflexive (canonical ResourceAlgebra.le_refl).
public export
tropLeRefl : (a : TropCost) -> tropLe a a
tropLeRefl = tropAddIdem

||| |<=| is transitive (canonical ResourceAlgebra.le_trans):
||| a|+|c = a|+|(b|+|c) = (a|+|b)|+|c = b|+|c = c.
public export
tropLeTrans : {a, b, c : TropCost} -> tropLe a b -> tropLe b c -> tropLe a c
tropLeTrans {a} {b} {c} ab bc =
  rewrite sym bc in
  rewrite tropAddAssoc a b c in
  rewrite ab in Refl

||| |+| is monotone in its right argument (canonical add_le_add_left):
||| (c|+|a)|+|(c|+|b) = c|+|b  when  a|+|b = b.
public export
tropAddMonoR : {a, b : TropCost} -> (c : TropCost) ->
               tropLe a b -> tropLe (tropAdd c a) (tropAdd c b)
tropAddMonoR {a} {b} c ab =
  let eMid : (tropAdd (tropAdd c a) c = tropAdd c a)
      eMid = trans (sym (tropAddAssoc c a c))
             (trans (cong (tropAdd c) (tropAddComm a c))
             (trans (tropAddAssoc c c a)
                    (cong (\x => tropAdd x a) (tropAddIdem c))))
  in trans (tropAddAssoc (tropAdd c a) c b)
     (trans (cong (\x => tropAdd x b) eMid)
     (trans (sym (tropAddAssoc c a b))
            (cong (tropAdd c) ab)))

||| |x| is monotone in its right argument (canonical mul_le_mul_left):
||| (c|x|a)|+|(c|x|b) = c|x|(a|+|b) = c|x|b.
public export
tropMulMonoR : {a, b : TropCost} -> (c : TropCost) ->
               tropLe a b -> tropLe (tropMul c a) (tropMul c b)
tropMulMonoR {a} {b} c ab =
  rewrite sym (tropMulDistrib c a b) in cong (tropMul c) ab

||| |x| is monotone in its left argument (canonical mul_le_mul_right).
public export
tropMulMonoL : {a, b : TropCost} -> (c : TropCost) ->
               tropLe a b -> tropLe (tropMul a c) (tropMul b c)
tropMulMonoL {a} {b} c ab =
  rewrite sym (tropMulDistribR a b c) in cong (\x => tropMul x c) ab

-- ============================================================================
-- Min-max / bottleneck layer  (Resource.Instances.MinMax + Bridge.hub_ceiling)
-- ============================================================================
--
-- Mirrors Resource/Instances/MinMax.lean + Resource/Bridge.lean @ 2e35229.
-- The min-max (bottleneck) semiring shares the choice operation |+| = min
-- (tropAdd) but composes sequentially by the WORST step (max) rather than by
-- sum.  Memory fact: MinMax / hub_ceiling = the bottleneck axis; one shared hub
-- caps fidelity.  Infinity (+inf) absorbs under max (an unreachable step makes
-- the whole route unreachable).

private
natMax : Nat -> Nat -> Nat
natMax Z n = n
natMax (S m) Z = S m
natMax (S m) (S n) = S (natMax m n)

private
natMaxComm : (m, n : Nat) -> natMax m n = natMax n m
natMaxComm Z Z = Refl
natMaxComm Z (S n) = Refl
natMaxComm (S m) Z = Refl
natMaxComm (S m) (S n) = cong S (natMaxComm m n)

private
tropMinZeroRight : (k : Nat) -> tropMin k Z = Z
tropMinZeroRight Z = Refl
tropMinZeroRight (S k) = Refl

||| min (max m n) m = m : a lower bottleneck absorbs against the route max.
private
tropMinMaxAbsorbL : (m, n : Nat) -> tropMin (natMax m n) m = m
tropMinMaxAbsorbL Z n = tropMinZeroRight n
tropMinMaxAbsorbL (S m) Z = cong S (tropMinIdem m)
tropMinMaxAbsorbL (S m) (S n) = cong S (tropMinMaxAbsorbL m n)

||| Bottleneck sequential composition: the worse (bottleneck) step.  Infinity
||| absorbs.  Mirrors canonical MinMax.mul (= max).
public export
tropMax : TropCost -> TropCost -> TropCost
tropMax Infinity _ = Infinity
tropMax _ Infinity = Infinity
tropMax (Finite a) (Finite b) = Finite (natMax a b)

||| Bottleneck composition is commutative.
public export
tropMaxComm : (a, b : TropCost) -> tropMax a b = tropMax b a
tropMaxComm Infinity Infinity = Refl
tropMaxComm Infinity (Finite n) = Refl
tropMaxComm (Finite m) Infinity = Refl
tropMaxComm (Finite m) (Finite n) = cong Finite (natMaxComm m n)

||| The bottleneck of two grades is no better (in |<=|) than the left one.
public export
tropMaxUpperL : (a, b : TropCost) -> tropLe (tropMax a b) a
tropMaxUpperL Infinity b = Refl
tropMaxUpperL (Finite m) Infinity = Refl
tropMaxUpperL (Finite m) (Finite n) = cong Finite (tropMinMaxAbsorbL m n)

||| ...nor than the right one.
public export
tropMaxUpperR : (a, b : TropCost) -> tropLe (tropMax a b) b
tropMaxUpperR a b = rewrite tropMaxComm a b in tropMaxUpperL b a

||| The bottleneck grade of a path: the worst step along it (Infinity if any
||| step is unreachable; Finite 0 for the empty path).
public export
pathBottleneck : List TropCost -> TropCost
pathBottleneck []        = Finite 0
pathBottleneck (x :: xs) = tropMax x (pathBottleneck xs)

||| **hub_ceiling.**  A path's bottleneck grade is |<=| (no better than) the
||| grade of every edge it routes through — one shared hub caps the fidelity of
||| everything passing through it.  Mirrors canonical Bridge.hub_ceiling_le.
public export
hubCeiling : {edges : List TropCost} -> (e : TropCost) ->
             Elem e edges -> tropLe (pathBottleneck edges) e
hubCeiling {edges = (e :: xs)} e Here =
  tropMaxUpperL e (pathBottleneck xs)
hubCeiling {edges = (y :: xs)} e (There later) =
  tropLeTrans (tropMaxUpperR y (pathBottleneck xs)) (hubCeiling e later)

-- ============================================================================
-- Residue measure — Echo residues measured into the tropical grade
-- ============================================================================
--
-- Mirrors Resource/EchoBridge.lean @ 2e35229.  Direction is strictly E -> R:
-- an opaque residue carrier E (the TypedWasm.ABI.Echo.EchoR residue carrier)
-- is MEASURED into this resource algebra (TropCost) via its sequential-
-- composition monoid (tropMul, Finite 0).  E is NOT a resource algebra; only
-- TropCost is.  Estate semantics (see Echo.idr cross-ref): the measured grade
-- IS the echo "structural irrecoverability" — loss accumulates by tropMul (+),
-- the tropical product, exactly the canonical accumulation mu : D_r D_s ->
-- D_{r+s}.

public export
record ResidueMeasure (E : Type) where
  constructor MkResidueMeasure
  ||| How two residues accumulate (the Echo-side operation, opaque here).
  combine        : E -> E -> E
  ||| The null residue.
  empty          : E
  ||| The measurement of a residue as a tropical grade.
  measure        : E -> TropCost
  ||| The empty residue measures as the multiplicative identity Finite 0.
  measureEmpty   : measure empty = Finite 0
  ||| Accumulating residues composes (tropMul) their grades.
  measureCombine : (e1, e2 : E) ->
                   measure (combine e1 e2) = tropMul (measure e1) (measure e2)

||| Combining with the empty residue on the left is grade-neutral.
public export
measureCombineEmptyLeft : (rm : ResidueMeasure e) -> (x : e) ->
                          rm.measure (rm.combine rm.empty x) = rm.measure x
measureCombineEmptyLeft rm x =
  rewrite rm.measureCombine rm.empty x in
  rewrite rm.measureEmpty in
  tropMulLeftId (rm.measure x)

||| Combining with the empty residue on the right is grade-neutral.
public export
measureCombineEmptyRight : (rm : ResidueMeasure e) -> (x : e) ->
                           rm.measure (rm.combine x rm.empty) = rm.measure x
measureCombineEmptyRight rm x =
  rewrite rm.measureCombine x rm.empty in
  rewrite rm.measureEmpty in
  tropMulRightId (rm.measure x)

private
lengthAppend' : (xs, ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthAppend' []        ys = Refl
lengthAppend' (x :: xs) ys = cong S (lengthAppend' xs ys)

||| A worked residue measure: count residue events into the tropical grade,
||| accumulating sequentially (tropMul = +).  Mirrors canonical
||| echoResidueAsMaxPlusCost (here over the min-plus carrier).  Proves the
||| E -> R direction is genuinely inhabited; List Unit never becomes a resource
||| algebra.
public export
echoResidueCost : ResidueMeasure (List Unit)
echoResidueCost = MkResidueMeasure
  (++)
  []
  (\l => Finite (length l))
  Refl
  (\e1, e2 => cong Finite (lengthAppend' e1 e2))

-- ============================================================================
-- Level 11 bottleneck obligation (wires hubCeiling into the L11 surface)
-- ============================================================================
--
-- The min-max / bottleneck cost model as a Level-11 proof obligation,
-- complementing Level11Proof (sequential sum, tropMul) and Level11KleeneProof
-- (all-pairs shortest path).  This is the worst-step / hub_ceiling cost model
-- (Resource.Instances.MinMax); it serves the bag-of-actions routing use case
-- ("one shared hub caps fidelity").  Registered in the certificate aggregator
-- via Proofs.attestL11_Bottleneck.

||| A Level-11 bottleneck cost certificate: the worst step along an access path,
||| proven to respect a declared bound.
public export
record Level11BottleneckProof where
  constructor MkLevel11Bottleneck
  ||| Per-edge access costs along the path.
  edges        : List TropCost
  ||| The certified worst-step (bottleneck) grade.
  bottleneck   : TropCost
  ||| The bottleneck is exactly the path's worst step.
  isBottleneck : bottleneck = pathBottleneck edges
  ||| Declared bound for this path.
  bound        : Nat
  ||| Proof the bottleneck respects the bound.
  bounded      : CostBounded bottleneck bound

||| hub_ceiling at the obligation level: every edge on a certified bottleneck
||| path is |>=| the certified bottleneck grade (i.e. `tropLe bottleneck edge`).
||| A direct consumer of `hubCeiling`.
public export
bottleneckCeilsEdges : (p : Level11BottleneckProof) -> (e : TropCost) ->
                       Elem e p.edges -> tropLe p.bottleneck e
bottleneckCeilsEdges p e el = rewrite p.isBottleneck in hubCeiling e el
