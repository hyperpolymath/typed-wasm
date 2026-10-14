-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceAlgebra.idr — the grade kernel of the typed-wasm ABI.
--
-- One parametric resource algebra, three instances (Loss, MaxPlus, HWM),
-- and the witnesses that say why they must stay three.  Every grade the ABI
-- carries (L11 cost, L12 staleness, L13 occupancy, L16 choreography) is
-- drawn from here; no other module defines a min-plus or max-plus algebra
-- (tools/check-grade-kernel.sh enforces that).
--
-- PROVENANCE.  Transcribed from hyperpolymath/resource-algebra
--   src/ResourceAlgebra/Core.agda @ cf9235c532712a783a404c359a1055f40134794a
-- (fetched by scripts/fetch-siblings.sh).  Agda --safe --without-K is the
-- proof kernel; this Idris2 module is the ABI layer and re-proves the same
-- laws.  Correspondence status: ASSUMED (transcription).  The instance
-- operation tables are additionally checked on both sides, by Agda `refl`
-- against the pinned sources and by Idris2 `Refl` against this port
-- (tests/transcription).  Nothing mechanical relates the two proofs.
--
-- Transcription map (Agda -> Idris2):
--   record ResourceAlgebra (Grade field)  -> interface ResourceAlgebra g
--   _⊕_ / _⊗_ / 𝟘 / 𝟙                    -> oplus / otimes / zeroG / oneG
--   alt : IsAltMonoid (assoc comm idem unitˡ) -> altAssoc altComm altIdem altUnitL
--   seq : IsSeqMonoid (assoc unitˡ unitʳ)     -> seqAssoc seqUnitL seqUnitR
--   _≼_                                   -> LeG
--   IsOrdered / IsDioid / IsAnnihilating  -> interfaces of the same names
--   IsDioid.ordered                       -> dioidMonoL / dioidMonoR (+ the
--                                            named implementation dioidOrdered)
-- The two monoid records are flattened into the one interface (Idris2 has no
-- convenient way to parameterise an interface by its own operations); the
-- fields and their directions are unchanged.
--
-- Layering, from weakest to strongest (as in Core.agda):
--   ResourceAlgebra  alternatives an idempotent commutative monoid (⊕, 𝟘),
--                    sequence a monoid (⊗, 𝟙).  All K-CUT-LOSS needs.
--   IsOrdered        ⊗ monotone for the ⊕-induced order; what a bound needs.
--   IsDioid          ⊗ distributes over ⊕; every dioid is ordered (proved).
--   IsAnnihilating   𝟘 absorbs under ⊗.  Separate on purpose: HWM is a dioid
--                    with 𝟘 = 𝟙, so it cannot be annihilating.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.ResourceAlgebra

%default total

-- ============================================================================
-- The algebra
-- ============================================================================

||| A grade algebra: alternatives form an idempotent commutative monoid
||| (`oplus`, `zeroG`); sequence forms a monoid (`otimes`, `oneG`).
public export
interface ResourceAlgebra g where
  ||| Alternatives (⊕).
  oplus  : g -> g -> g
  ||| Sequence (⊗).
  otimes : g -> g -> g
  ||| Unit of alternatives (𝟘).
  zeroG  : g
  ||| Unit of sequence (𝟙).
  oneG   : g
  -- IsAltMonoid oplus zeroG
  altAssoc : (a, b, c : g) -> oplus (oplus a b) c = oplus a (oplus b c)
  altComm  : (a, b : g) -> oplus a b = oplus b a
  altIdem  : (a : g) -> oplus a a = a
  altUnitL : (a : g) -> oplus zeroG a = a
  -- IsSeqMonoid otimes oneG
  seqAssoc : (a, b, c : g) -> otimes (otimes a b) c = otimes a (otimes b c)
  seqUnitL : (a : g) -> otimes oneG a = a
  seqUnitR : (a : g) -> otimes a oneG = a

||| Agda `IsAltMonoid.unitʳ`.
public export
altUnitR : ResourceAlgebra g => (a : g) -> oplus a (zeroG {g}) = a
altUnitR a = trans (altComm a zeroG) (altUnitL a)

-- ============================================================================
-- The induced order: a ≼ b when b absorbs a
-- ============================================================================
--
-- Which way it runs numerically is instance-specific (Separation.idr): in
-- MaxPlus  1 ≼ 2;  in Loss the numerically smaller grade is ABOVE.

||| Agda `_≼_`.
public export
LeG : ResourceAlgebra g => g -> g -> Type
LeG a b = oplus a b = b

||| Agda `≼-refl`.
public export
leRefl : ResourceAlgebra g => (a : g) -> LeG a a
leRefl a = altIdem a

||| Agda `≼-trans`.
public export
leTrans : ResourceAlgebra g => {a, b, c : g} -> LeG a b -> LeG b c -> LeG a c
leTrans {a} {b} {c} p q =
  trans (cong (oplus a) (sym q))
  (trans (sym (altAssoc a b c))
  (trans (cong (\x => oplus x c) p) q))

||| Agda `≼-antisym`.
public export
leAntisym : ResourceAlgebra g => {a, b : g} -> LeG a b -> LeG b a -> a = b
leAntisym {a} {b} p q = trans (sym q) (trans (altComm b a) p)

||| Agda `𝟘-least`.
public export
zeroLeast : ResourceAlgebra g => (a : g) -> LeG (zeroG {g}) a
zeroLeast a = altUnitL a

||| Agda `⊕-upperˡ`.
public export
oplusUpperL : ResourceAlgebra g => (a, b : g) -> LeG a (oplus a b)
oplusUpperL a b =
  trans (sym (altAssoc a a b)) (cong (\x => oplus x b) (altIdem a))

||| Agda `⊕-upperʳ`.
public export
oplusUpperR : ResourceAlgebra g => (a, b : g) -> LeG b (oplus a b)
oplusUpperR a b =
  trans (cong (oplus b) (altComm a b))
  (trans (sym (altAssoc b b a))
  (trans (cong (\x => oplus x a) (altIdem b))
         (altComm b a)))

||| Agda `⊕-interchange`.
public export
oplusInterchange : ResourceAlgebra g => (a, b, c, d : g) ->
                   oplus (oplus a b) (oplus c d) = oplus (oplus a c) (oplus b d)
oplusInterchange a b c d =
  trans (altAssoc a b (oplus c d))
  (trans (cong (oplus a)
    (trans (sym (altAssoc b c d))
    (trans (cong (\x => oplus x d) (altComm b c))
           (altAssoc c b d))))
  (sym (altAssoc a c (oplus b d))))

||| Alternatives are monotone in every resource algebra.  Agda `⊕-mono`.
public export
oplusMono : ResourceAlgebra g => {a, a', b, b' : g} ->
            LeG a a' -> LeG b b' -> LeG (oplus a b) (oplus a' b')
oplusMono {a} {a'} {b} {b'} p q =
  trans (oplusInterchange a b a' b') (cong2 oplus p q)

-- ============================================================================
-- IsOrdered — sequencing is monotone
-- ============================================================================

||| Agda `IsOrdered`.
public export
interface ResourceAlgebra g => IsOrdered g where
  otimesMonoL : (c : g) -> {a, b : g} -> LeG a b -> LeG (otimes c a) (otimes c b)
  otimesMonoR : (c : g) -> {a, b : g} -> LeG a b -> LeG (otimes a c) (otimes b c)

||| Agda `IsOrdered.⊗-mono`.
public export
otimesMono : IsOrdered g => {a, a', b, b' : g} ->
             LeG a a' -> LeG b b' -> LeG (otimes a b) (otimes a' b')
otimesMono {a} {a'} {b} {b'} p q = leTrans (otimesMonoR b p) (otimesMonoL a' q)

-- ============================================================================
-- IsDioid — distributivity, and hence order
-- ============================================================================

||| Agda `IsDioid`.
public export
interface ResourceAlgebra g => IsDioid g where
  distribL : (a, b, c : g) -> otimes a (oplus b c) = oplus (otimes a b) (otimes a c)
  distribR : (a, b, c : g) -> otimes (oplus a b) c = oplus (otimes a c) (otimes b c)

||| Distributivity gives left monotonicity outright.  Agda `IsDioid.ordered`
||| (its ⊗-monoˡ field).
public export
dioidMonoL : IsDioid g => (c : g) -> {a, b : g} -> LeG a b -> LeG (otimes c a) (otimes c b)
dioidMonoL c {a} {b} p = trans (sym (distribL c a b)) (cong (otimes c) p)

||| Agda `IsDioid.ordered` (its ⊗-monoʳ field).
public export
dioidMonoR : IsDioid g => (c : g) -> {a, b : g} -> LeG a b -> LeG (otimes a c) (otimes b c)
dioidMonoR c {a} {b} p = trans (sym (distribR a b c)) (cong (\x => otimes x c) p)

||| Every dioid is ordered — Agda `IsDioid.ordered : IsOrdered R`, as a named
||| implementation (so it is available with `using`, but never competes with
||| an instance's own `IsOrdered` during search).
public export
[dioidOrdered] IsDioid g => IsOrdered g where
  otimesMonoL = dioidMonoL
  otimesMonoR = dioidMonoR

-- ============================================================================
-- IsAnnihilating — 𝟘 absorbs under ⊗
-- ============================================================================

||| Agda `IsAnnihilating`.  Independent of IsDioid: Instances/HWM is a dioid
||| with no annihilating zero (tests/reject/HWMAnnihilates.idr is the control).
public export
interface ResourceAlgebra g => IsAnnihilating g where
  annihilL : (a : g) -> otimes (zeroG {g}) a = zeroG {g}
  annihilR : (a : g) -> otimes a (zeroG {g}) = zeroG {g}
