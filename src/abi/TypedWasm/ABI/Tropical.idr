-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Tropical.idr — Level 11: Tropical cost-tracking for memory access
--
-- Every memory access operation carries a cost.  Three cost models live
-- here, and they are three different algebras (do not conflate them):
--   * sequential path cost and all-pairs CHEAPEST path (Level11Proof,
--     Level11KleeneProof): min-plus — the grade kernel's Loss carrier;
--   * the BOTTLENECK (worst step) of a path (Level11BottleneckProof):
--     min-max — choice by min, sequence by max, +inf absorbing.  It is not
--     max-plus and has no kernel instance (resource-algebra has no MinMax);
--   * worst-case cost over alternatives would be max-plus
--     (ResourceAlgebra/MaxPlus.idr); no L11 obligation uses it yet.
-- The type checker proves that an access path through shared memory has
-- bounded cost.
--
-- This is the "how expensive is this access pattern?" question answered
-- at compile time. It prevents pathological access patterns (e.g. a
-- tight loop doing random access across cache lines) from compiling
-- without an explicit cost annotation acknowledging the expense.
--
-- ----------------------------------------------------------------------------
-- Grade kernel (PWL-01, 2026-10-14).  TropCost IS the kernel's Loss carrier
-- (TypedWasm.ABI.ResourceAlgebra.Loss, transcribed from hyperpolymath/
-- resource-algebra Instances/Loss.agda @ cf9235c): tropAdd = lossAlt (min),
-- tropMul = lossSeq (+), Infinity = 𝟘, Finite 0 = 𝟙.  The twelve semiring
-- axioms and the dioid-order layer below are DERIVED from the kernel's
-- instance proofs; nothing here re-defines min-plus.  007-lang's
-- TropicalSemiring.idr (the source of the A2 port, 2026-04-18) and
-- tropical-resource-typing @ 2e35229 (Lean4, the earlier canonical axis) are
-- provenance, not parallel definitions.
--
-- Still NOT mirrored (debt, owner decision):
--   * parametric_resource_transport — needs resource-algebra homomorphisms.
--     Upstream has them since 0b338c9 (Morphism.agda: strict and lax); they
--     are not ported here.
-- The bottleneck layer (tropMax below) is the kernel's MinMax sequence
-- (ResourceAlgebra/MinMax.idr), so no grade operation is defined here.
-- typed-wasm holds one thing the kernel lacks: the Kleene-closure matrix
-- layer below (extend-upstream candidate; owner sign-off required).
-- ----------------------------------------------------------------------------

module TypedWasm.ABI.Tropical

import TypedWasm.ABI.Region
import TypedWasm.ABI.Levels
import public TypedWasm.ABI.ResourceAlgebra
import public TypedWasm.ABI.ResourceAlgebra.Loss
import public TypedWasm.ABI.ResourceAlgebra.MaxPlus
import public TypedWasm.ABI.ResourceAlgebra.MinMax
import Data.Nat
import Data.Fin
import Data.List
import Data.List.Elem

%default total

-- ============================================================================
-- Tropical Semiring — the kernel's Loss instance
-- ============================================================================

||| A min-plus cost: `Finite n` or `Infinity` (unreachable / unbounded).
||| This is the kernel's Loss carrier; addition is min, multiplication is
||| plus, Infinity is the zero element and `Finite 0` the unit.
public export
TropCost : Type
TropCost = LossGrade

||| Tropical addition: min of two costs.  The kernel's `lossAlt`.
public export
tropAdd : TropCost -> TropCost -> TropCost
tropAdd = lossAlt

||| Tropical multiplication: sum of two costs (path composition).  The
||| kernel's `lossSeq`.
public export
tropMul : TropCost -> TropCost -> TropCost
tropMul = lossSeq

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
-- Tropical semiring laws — all twelve axioms, derived from the kernel
-- ============================================================================
--
-- Each law below is the kernel's Loss-instance proof
-- (TypedWasm.ABI.ResourceAlgebra.Loss), restated in this module's historic
-- names and directions so existing consumers keep compiling.  The one law
-- the kernel does not carry — commutativity of sequence — is a fact about
-- this instance (ℕ addition commutes), proved here from base's
-- plusCommutative; it is not a re-definition of the algebra.

-- ---- Additive monoid: (TropCost, tropAdd, Infinity) ----

||| Left identity: tropAdd Infinity a = a.  Kernel `altUnitL`.
public export
tropAddLeftId : (a : TropCost) -> tropAdd Infinity a = a
tropAddLeftId a = altUnitL a

||| Right identity: tropAdd a Infinity = a.  Kernel `altUnitR`.
public export
tropAddRightId : (a : TropCost) -> tropAdd a Infinity = a
tropAddRightId a = altUnitR a

||| Commutativity: tropAdd a b = tropAdd b a.  Kernel `lossAltComm`.
|||
||| The order of two branch alternatives does not affect which one wins.
public export
tropAddComm : (a, b : TropCost) -> tropAdd a b = tropAdd b a
tropAddComm = lossAltComm

||| Associativity: tropAdd a (tropAdd b c) = tropAdd (tropAdd a b) c.
||| Kernel `lossAltAssoc`, read right to left.
|||
||| Grouping three branch alternatives does not affect the minimum outcome.
public export
tropAddAssoc : (a, b, c : TropCost) ->
               tropAdd a (tropAdd b c) = tropAdd (tropAdd a b) c
tropAddAssoc a b c = sym (lossAltAssoc a b c)

-- ---- Multiplicative monoid: (TropCost, tropMul, Finite 0) ----

||| Left identity: tropMul (Finite 0) a = a.  Kernel `lossSeqUnitL`.
public export
tropMulLeftId : (a : TropCost) -> tropMul (Finite 0) a = a
tropMulLeftId = lossSeqUnitL

||| Right identity: tropMul a (Finite 0) = a.  Kernel `lossSeqUnitR`.
public export
tropMulRightId : (a : TropCost) -> tropMul a (Finite 0) = a
tropMulRightId = lossSeqUnitR

||| Commutativity: tropMul a b = tropMul b a.  Instance fact (ℕ + commutes);
||| the kernel's sequence is only a monoid.
|||
||| Sequential costs compose the same in either order.
public export
tropMulComm : (a, b : TropCost) -> tropMul a b = tropMul b a
tropMulComm Infinity   Infinity   = Refl
tropMulComm Infinity   (Finite _) = Refl
tropMulComm (Finite _) Infinity   = Refl
tropMulComm (Finite m) (Finite n) = cong Finite (plusCommutative m n)

||| Associativity: tropMul a (tropMul b c) = tropMul (tropMul a b) c.
||| Kernel `lossSeqAssoc`, read right to left.
|||
||| Parenthesisation does not affect the cost of a sequential chain.
public export
tropMulAssoc : (a, b, c : TropCost) ->
               tropMul a (tropMul b c) = tropMul (tropMul a b) c
tropMulAssoc a b c = sym (lossSeqAssoc a b c)

-- ---- Annihilation: Infinity annihilates tropMul ----

||| Left annihilation: tropMul Infinity a = Infinity.  Kernel `annihilL`.
public export
tropMulLeftAnn : (a : TropCost) -> tropMul Infinity a = Infinity
tropMulLeftAnn a = annihilL a

||| Right annihilation: tropMul a Infinity = Infinity.  Kernel `lossAnnihilR`.
public export
tropMulRightAnn : (a : TropCost) -> tropMul a Infinity = Infinity
tropMulRightAnn = lossAnnihilR

-- ---- Distributivity ----

||| Left distributivity:
||| tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c).
||| Kernel `lossDistribL`.
|||
||| A constant sequential prefix does not change which branch is cheaper.
public export
tropMulDistrib : (a, b, c : TropCost) ->
                 tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c)
tropMulDistrib = lossDistribL

||| Right distributivity:
||| tropMul (tropAdd a b) c = tropAdd (tropMul a c) (tropMul b c).
||| Kernel `lossDistribR` (formerly derived here from left distributivity +
||| tropMulComm; the kernel proves it directly).
public export
tropMulDistribR : (a, b, c : TropCost) ->
                  tropMul (tropAdd a b) c = tropAdd (tropMul a c) (tropMul b c)
tropMulDistribR = lossDistribR

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
-- Ordered layer — the kernel's dioid order
-- ============================================================================
--
-- The kernel order (TypedWasm.ABI.ResourceAlgebra.LeG, Agda `_≼_`) is
--   a ≼ b  :=  oplus a b = b
-- For this Loss instance oplus = min, so the order is the REVERSE of numeric
-- <=: Finite m ≼ Finite n  iff  n <= m, and Infinity (the additive zero /
-- +inf) is the LEAST element.  Smaller cost sits higher (resource-algebra
-- Separation S-3; ResourceAlgebra/Separation.idr `lossOrderReversed`).
-- Every lemma here is the kernel's generic one at TropCost.

||| The dioid order: a refines b iff combining them is b.  Kernel `LeG`.
public export
tropLe : TropCost -> TropCost -> Type
tropLe a b = LeG a b

||| TropCost addition is idempotent (the dioid property).  Kernel `lossAltIdem`.
public export
tropAddIdem : (a : TropCost) -> tropAdd a a = a
tropAddIdem = lossAltIdem

||| ≼ is reflexive.  Kernel `leRefl`.
public export
tropLeRefl : (a : TropCost) -> tropLe a a
tropLeRefl a = leRefl a

||| ≼ is transitive.  Kernel `leTrans`.
public export
tropLeTrans : {a, b, c : TropCost} -> tropLe a b -> tropLe b c -> tropLe a c
tropLeTrans ab bc = leTrans ab bc

||| oplus is monotone in its right argument.  Kernel `oplusMono` with the
||| left argument fixed.
public export
tropAddMonoR : {a, b : TropCost} -> (c : TropCost) ->
               tropLe a b -> tropLe (tropAdd c a) (tropAdd c b)
tropAddMonoR c ab = oplusMono (leRefl c) ab

||| otimes is monotone in its right argument.  Kernel `otimesMonoL`
||| (IsOrdered LossGrade, obtained from IsDioid by `dioidMonoL`).
public export
tropMulMonoR : {a, b : TropCost} -> (c : TropCost) ->
               tropLe a b -> tropLe (tropMul c a) (tropMul c b)
tropMulMonoR c ab = otimesMonoL c ab

||| otimes is monotone in its left argument.  Kernel `otimesMonoR`.
public export
tropMulMonoL : {a, b : TropCost} -> (c : TropCost) ->
               tropLe a b -> tropLe (tropMul a c) (tropMul b c)
tropMulMonoL c ab = otimesMonoR c ab

-- ============================================================================
-- Min-max / bottleneck layer  (Resource.Instances.MinMax + Bridge.hub_ceiling)
-- ============================================================================
--
-- Mirrors tropical-resource-typing Resource/Instances/MinMax.lean +
-- Resource/Bridge.lean @ 2e35229.  The min-max (bottleneck) semiring shares
-- the choice operation with Loss (oplus = min) but composes sequentially by
-- the WORST step (max) rather than by sum.  One shared hub caps fidelity.
-- Infinity (+inf) absorbs under max (an unreachable step makes the whole
-- route unreachable).
--
-- This is NOT max-plus: max-plus takes max over ALTERNATIVES and sums along
-- a path, with −∞ as its zero (ResourceAlgebra/MaxPlus.idr); here max is
-- the SEQUENCE operation, +∞ absorbs, and alternatives stay min.  It is the
-- kernel's MinMax instance (ResourceAlgebra/MinMax.idr, transcribed from
-- resource-algebra Instances/MinMax.agda); `tropMax` is its sequence, not a
-- copy of it.

||| min (max m n) m = m : a lower bottleneck absorbs against the route max.
private
tropMinMaxAbsorbL : (m, n : Nat) -> minimum (maximum m n) m = m
tropMinMaxAbsorbL Z     n     = minimumZeroZeroLeft n
tropMinMaxAbsorbL (S m) Z     = cong S (minimumIdempotent m)
tropMinMaxAbsorbL (S m) (S n) = cong S (tropMinMaxAbsorbL m n)

||| Bottleneck sequential composition: the worse (bottleneck) step.  Infinity
||| absorbs.  The kernel's MinMax sequence (`minMaxSeq`, Agda `_⊔g_`).
public export
tropMax : TropCost -> TropCost -> TropCost
tropMax = minMaxSeq

||| Bottleneck composition is commutative.
public export
tropMaxComm : (a, b : TropCost) -> tropMax a b = tropMax b a
tropMaxComm Infinity Infinity = Refl
tropMaxComm Infinity (Finite n) = Refl
tropMaxComm (Finite m) Infinity = Refl
tropMaxComm (Finite m) (Finite n) = cong Finite (maximumCommutative m n)

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

-- ============================================================================
-- Level 11 obligations as kernel instantiations (PWL-01 step 2)
-- ============================================================================
--
-- Each L11 obligation below is read through the grade kernel, so promoting
-- L11 is a matter of instantiating kernel lemmas, not of a new algebra:
--
--   Level11Proof / Level11KleeneProof   Loss (min-plus).  The numeric bound
--       `CostBounded c n` IS the kernel order `Finite n ≼ c` (Loss's order is
--       ℕ's reversed: the cost sits above its bound), and bounds compose
--       along a path by the kernel's `otimesMono` (IsOrdered LossGrade).
--   Level11WorstCaseProof               MaxPlus (max-plus).  A branching
--       access plan's worst case: max over alternatives, sum along a
--       sequence; the bound is `worstCase plan ≼ Val bound`, which is ℕ's ≤.
--       DESIGNED as an obligation: no surface syntax, checker or attestation
--       uses it yet.
--   Level11BottleneckProof              MinMax (min-max), the kernel instance
--       ResourceAlgebra/MinMax.idr: `tropMax` is its sequence.  NOT MaxPlus
--       (tests/reject/TropicalIsNotMaxPlus.idr) and NOT Loss
--       (tests/reject/MinMaxIsLoss.idr).

||| The L11 numeric bound is the kernel's Loss order: `c ≤ n` as a cost is
||| `Finite n ≼ c` as a grade.
public export
costBoundedIsLossOrder : {c : TropCost} -> {n : Nat} -> CostBounded c n -> LeG (Finite n) c
costBoundedIsLossOrder (BoundedFinite le) = lossLeOfLTE le

||| ...and back: a grade above `Finite n` in the Loss order is a cost
||| bounded by n (in particular it is finite).
public export
lossOrderIsCostBounded : {n : Nat} -> (c : TropCost) -> LeG (Finite n) c -> CostBounded c n
lossOrderIsCostBounded (Finite k) prf = BoundedFinite (lteOfLossLe n k prf)
lossOrderIsCostBounded Infinity   prf = absurd (finiteNotLeInfinity prf)

||| Path bounds compose: bounded steps give a bounded path, with the bounds
||| added.  Kernel `otimesMono` (IsOrdered LossGrade), not a new proof.
public export
costBoundedSeq : {c1, c2 : TropCost} -> {n1, n2 : Nat} ->
                 CostBounded c1 n1 -> CostBounded c2 n2 ->
                 CostBounded (tropMul c1 c2) (n1 + n2)
costBoundedSeq b1 b2 =
  lossOrderIsCostBounded (tropMul c1 c2)
    (otimesMono (costBoundedIsLossOrder b1) (costBoundedIsLossOrder b2))

-- ---- MaxPlus: the worst case over alternatives ----

||| A branching access plan: a single access of known cost, one plan after
||| another, or one of two plans (which one runs is not known statically).
public export
data AccessPlan : Type where
  ||| One access of the given cost.
  Step  : (cost : Nat) -> AccessPlan
  ||| `p` then `q`.
  Then  : AccessPlan -> AccessPlan -> AccessPlan
  ||| Either `p` or `q`.
  OneOf : AccessPlan -> AccessPlan -> AccessPlan

||| The worst-case cost of a plan, graded in the kernel's MaxPlus instance:
||| costs add along `Then`, the dearer branch counts at `OneOf`.
public export
worstCase : AccessPlan -> MaxPlusGrade
worstCase (Step c)    = Val c
worstCase (Then p q)  = maxPlusSeq (worstCase p) (worstCase q)
worstCase (OneOf p q) = maxPlusAlt (worstCase p) (worstCase q)

||| A plan's worst case is always finite (never −∞): every plan does at
||| least its cheapest branch.
public export
worstCaseFinite : (p : AccessPlan) -> (w : Nat ** worstCase p = Val w)
worstCaseFinite (Step c)    = (c ** Refl)
worstCaseFinite (Then p q)  =
  let (a ** pa) = worstCaseFinite p
      (b ** qb) = worstCaseFinite q
  in (a + b ** rewrite pa in rewrite qb in Refl)
worstCaseFinite (OneOf p q) =
  let (a ** pa) = worstCaseFinite p
      (b ** qb) = worstCaseFinite q
  in (maximum a b ** rewrite pa in rewrite qb in Refl)

||| Level 11 worst-case obligation: the plan's worst case is within
||| `planBound` in the MaxPlus order (ℕ's ≤ on finite grades).
public export
record Level11WorstCaseProof where
  constructor MkLevel11WorstCase
  ||| The branching access plan.
  plan        : AccessPlan
  ||| The declared worst-case bound.
  planBound   : Nat
  ||| The plan's worst case does not exceed the bound.
  planBounded : LeG (worstCase plan) (Val planBound)

||| The bound read as a number: the worst case is `Val w` with w ≤ bound.
public export
worstCaseWithin : (prf : Level11WorstCaseProof) ->
                  (w : Nat ** (worstCase prf.plan = Val w, LTE w prf.planBound))
worstCaseWithin prf =
  let (w ** eq) = worstCaseFinite prf.plan
  in (w ** (eq, lteOfMaxPlusLe w prf.planBound
                  (replace {p = \g => LeG g (Val prf.planBound)} eq prf.planBounded)))

||| Sequenced plans: the bounds add.  Kernel `otimesMono` (IsOrdered
||| MaxPlusGrade).
public export
worstCaseThen : {p, q : AccessPlan} -> {a, b : Nat} ->
                LeG (worstCase p) (Val a) -> LeG (worstCase q) (Val b) ->
                LeG (worstCase (Then p q)) (Val (a + b))
worstCaseThen pa qb = otimesMono pa qb

||| Alternative plans: the larger bound covers both.  Kernel `oplusMono`.
public export
worstCaseOneOf : {p, q : AccessPlan} -> {a, b : Nat} ->
                 LeG (worstCase p) (Val a) -> LeG (worstCase q) (Val b) ->
                 LeG (worstCase (OneOf p q)) (Val (maximum a b))
worstCaseOneOf pa qb = oplusMono pa qb
