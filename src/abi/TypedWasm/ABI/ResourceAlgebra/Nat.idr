-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra/Nat.idr — the ℕ lemmas the grade kernel's instances need.
--
-- Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Prelude.agda @ cf9235c532712a783a404c359a1055f40134794a
-- Correspondence status: ASSUMED (transcription).
--
-- The Agda development is builtins-only, so it defines its own `max`, `min`
-- and `_≤_`.  Idris2's base library already has the same definitions, clause
-- for clause: `Data.Nat.maximum`, `Data.Nat.minimum` (structural on Z/S) and
-- `LTE` (LTEZero/LTESucc).  They are used here instead of being declared a
-- second time, together with base's associativity / commutativity /
-- idempotence / upper-bound lemmas.  This module holds only what base lacks.
--
-- Direction note: base states associativity as  l ∘ (c ∘ r) = (l ∘ c) ∘ r,
-- the Agda Prelude as  (m ∘ n) ∘ p ≡ m ∘ (n ∘ p).  `maxAssoc` below is the
-- Agda direction, so the proofs that follow read line-for-line like Agda's.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra.Nat

import Data.Nat

%default total

-- ============================================================================
-- Order on ℕ — Prelude.agda §order
-- ============================================================================

||| Agda `≤-refl`.
public export
lteRefl : (n : Nat) -> LTE n n
lteRefl Z     = LTEZero
lteRefl (S n) = LTESucc (lteRefl n)

||| Agda `≤-trans`.
public export
lteTrans : {m, n, p : Nat} -> LTE m n -> LTE n p -> LTE m p
lteTrans LTEZero     _           = LTEZero
lteTrans (LTESucc q) (LTESucc r) = LTESucc (lteTrans q r)

||| Agda `+-monoʳ-≤`.
public export
plusMonoRLTE : (m : Nat) -> {n, p : Nat} -> LTE n p -> LTE (m + n) (m + p)
plusMonoRLTE Z     q = q
plusMonoRLTE (S m) q = LTESucc (plusMonoRLTE m q)

||| Proofs of m ≤ n are unique.  Agda `≤-irrelevant` (Instances/HWM.agda).
public export
lteIrrelevant : {m, n : Nat} -> (p, q : LTE m n) -> p = q
lteIrrelevant LTEZero     LTEZero     = Refl
lteIrrelevant (LTESucc p) (LTESucc q) = cong LTESucc (lteIrrelevant p q)

-- ============================================================================
-- max (the join of the usual order on ℕ) — Prelude.agda §max
-- ============================================================================

||| Agda `max-assoc` (Agda's direction; base's `maximumAssociative` reversed).
public export
maxAssoc : (m, n, p : Nat) -> maximum (maximum m n) p = maximum m (maximum n p)
maxAssoc m n p = sym (maximumAssociative m n p)

||| A join absorbs its duplicate.  Agda `max-dup`.
public export
maxDup : (p, x, y : Nat) ->
         maximum (maximum p x) (maximum p y) = maximum p (maximum x y)
maxDup p x y =
  trans (maxAssoc p x (maximum p y))
  (trans (cong (maximum p) (sym (maxAssoc x p y)))
  (trans (cong (\z => maximum p (maximum z y)) (maximumCommutative x p))
  (trans (cong (maximum p) (maxAssoc p x y))
  (trans (sym (maxAssoc p p (maximum x y)))
         (cong (\z => maximum z (maximum x y)) (maximumIdempotent p))))))

||| Agda `max-interchange`.
public export
maxInterchange : (a, b, c, d : Nat) ->
                 maximum (maximum a b) (maximum c d)
               = maximum (maximum a c) (maximum b d)
maxInterchange a b c d =
  trans (maxAssoc a b (maximum c d))
  (trans (cong (maximum a)
    (trans (sym (maxAssoc b c d))
    (trans (cong (\z => maximum z d) (maximumCommutative b c))
           (maxAssoc c b d))))
  (sym (maxAssoc a c (maximum b d))))

||| Agda `+-distribˡ-max`.
public export
plusDistribLMax : (a, b, c : Nat) -> a + maximum b c = maximum (a + b) (a + c)
plusDistribLMax Z     b c = Refl
plusDistribLMax (S a) b c = cong S (plusDistribLMax a b c)

||| Agda `+-distribʳ-max`.
public export
plusDistribRMax : (a, b, c : Nat) -> maximum a b + c = maximum (a + c) (b + c)
plusDistribRMax a b c =
  trans (plusCommutative (maximum a b) c)
  (trans (plusDistribLMax c a b)
  (trans (cong (\z => maximum z (c + b)) (plusCommutative c a))
         (cong (maximum (a + c)) (plusCommutative c b))))

||| Agda `max-mono-≤`.
public export
maxMonoLTE : {a, a', b, b' : Nat} -> LTE a a' -> LTE b b' ->
             LTE (maximum a b) (maximum a' b')
maxMonoLTE {a' = a'}            LTEZero     q       =
  lteTrans q (maximumRightUpperBound a' _)
maxMonoLTE {a' = S k} {b' = b'} (LTESucc p) LTEZero =
  lteTrans (LTESucc p) (maximumLeftUpperBound (S k) b')
maxMonoLTE                      (LTESucc p) (LTESucc q) = LTESucc (maxMonoLTE p q)

||| A bounded argument is absorbed by max.  Agda `max-absorb-≤`
||| (Instances/HWM.agda).
public export
maxAbsorbLTE : {n, p : Nat} -> LTE n p -> maximum p n = p
maxAbsorbLTE {p} LTEZero     = maximumZeroNLeft p
maxAbsorbLTE     (LTESucc q) = cong S (maxAbsorbLTE q)

-- ============================================================================
-- min (the meet of the usual order on ℕ) — Prelude.agda §min
-- ============================================================================

||| Agda `min-assoc` (Agda's direction).
public export
minAssoc : (m, n, p : Nat) -> minimum (minimum m n) p = minimum m (minimum n p)
minAssoc m n p = sym (minimumAssociative m n p)

||| Agda `+-distribˡ-min`.
public export
plusDistribLMin : (a, b, c : Nat) -> a + minimum b c = minimum (a + b) (a + c)
plusDistribLMin Z     b c = Refl
plusDistribLMin (S a) b c = cong S (plusDistribLMin a b c)

||| Agda `+-distribʳ-min`.
public export
plusDistribRMin : (a, b, c : Nat) -> minimum a b + c = minimum (a + c) (b + c)
plusDistribRMin a b c =
  trans (plusCommutative (minimum a b) c)
  (trans (plusDistribLMin c a b)
  (trans (cong (\z => minimum z (c + b)) (plusCommutative c a))
         (cong (minimum (a + c)) (plusCommutative c b))))

-- ============================================================================
-- Addition — Prelude.agda §addition (Agda's direction for associativity)
-- ============================================================================

||| Agda `+-assoc`.
public export
plusAssoc : (m, n, p : Nat) -> (m + n) + p = m + (n + p)
plusAssoc m n p = sym (plusAssociative m n p)

-- ============================================================================
-- typed-wasm additions (NOT in the Agda source): min / max against ℕ's order
-- ============================================================================
--
-- Used to read the instances' induced orders as ℕ's order (Loss.idr,
-- MaxPlus.idr) and by the occupancy theorems (TypedWasm.ABI.Occupancy).

||| `S` is injective.
public export
succInj : {m, n : Nat} -> S m = S n -> m = n
succInj Refl = Refl

||| A bounded argument is what min returns.
public export
minimumOfLTE : {k, n : Nat} -> LTE k n -> minimum n k = k
minimumOfLTE {n} LTEZero     = minimumZeroZeroLeft n
minimumOfLTE     (LTESucc q) = cong S (minimumOfLTE q)

||| If min returns its right argument, that argument is the smaller.
public export
lteOfMinimum : (n, k : Nat) -> minimum n k = k -> LTE k n
lteOfMinimum n     Z     _   = LTEZero
lteOfMinimum Z     (S k) prf = absurd prf
lteOfMinimum (S n) (S k) prf = LTESucc (lteOfMinimum n k (succInj prf))

||| A smaller argument is absorbed by max.
public export
maximumOfLTE : {m, n : Nat} -> LTE m n -> maximum m n = n
maximumOfLTE LTEZero     = Refl
maximumOfLTE (LTESucc q) = cong S (maximumOfLTE q)

||| If max returns its right argument, the left one is the smaller.
public export
lteOfMaximum : (m, n : Nat) -> maximum m n = n -> LTE m n
lteOfMaximum Z     n     _   = LTEZero
lteOfMaximum (S m) Z     prf = absurd prf
lteOfMaximum (S m) (S n) prf = LTESucc (lteOfMaximum m n (succInj prf))

||| max is the least upper bound.  occupancy-types `max-lub` (Order.agda).
public export
maxLub : {a, b, c : Nat} -> LTE a c -> LTE b c -> LTE (maximum a b) c
maxLub LTEZero     q           = q
maxLub (LTESucc p) LTEZero     = LTESucc p
maxLub (LTESucc p) (LTESucc q) = LTESucc (maxLub p q)
