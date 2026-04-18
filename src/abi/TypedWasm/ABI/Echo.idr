-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Echo.idr — Echo types (displayed types / fibrations) over a base
--
-- An echo type over B is a type family P : B -> Type; equivalently a
-- fibration presented by its fibers.  Every dependent family P : B -> Type
-- is an echo type in this sense.  The fiber-of-a-map construction below
-- is the canonical way to build one.
--
-- Ported from ~/Desktop/EchoFibers.agda and generalised to the
-- displayed-type view.  The slice-category morphism structure
-- (HomOver, echoMap, echoMapSquare) and its functor laws are preserved.
--
-- Why typed-wasm wants this:
--   * Every level's witness type is already an echo type over its index
--     (RegionSchema over RegionId; Attestation over Level; Accessible over
--     ModuleId; EffectProof over EffectSet; ...).
--   * Crossing-boundary lemmas (multi-module, cross-language ABI) factor
--     through echoMapSquare — the cartesian-lift structure gives the
--     coherence for free.
--   * Proofs.idr ceremonial attestations become attestations tied to
--     echo-type witnesses: you cannot mint an attestation without a
--     preimage in the relevant fiber.
--
-- NO believe_me, NO postulate, NO assert_total, NO Admitted.
-- %default total.

module TypedWasm.ABI.Echo

%default total

-- Shadow the prelude's trans with a definition that reduces on the first
-- Refl alone.  The prelude version (trans Refl Refl = Refl) does not
-- reduce trans Refl q to q definitionally, which the functor laws below
-- rely on.
%hide Builtin.trans

-- ============================================================================
-- Local equational reasoning
-- ============================================================================

||| Transitivity of propositional equality.  Mirrors Agda's
||| `trans refl q = q` — reduces on the first argument alone, which the
||| echo-map functor laws exploit definitionally.
public export
trans : {0 A : Type} -> {0 x, y, z : A} -> x = y -> y = z -> x = z
trans Refl q = q

||| Associativity of transitivity (the "pentagon" coherence used by
||| echoMapCompose).
public export
transAssoc : {0 A : Type} -> {0 w, x, y, z : A}
          -> (p : w = x) -> (q : x = y) -> (r : y = z)
          -> trans (trans p q) r = trans p (trans q r)
transAssoc Refl _ _ = Refl

-- ============================================================================
-- Displayed types (the general echo-type concept)
-- ============================================================================

||| A displayed type over B (equivalently: a fibration, or a type family
||| indexed by B).  Every dependent P : B -> Type is an echo type in this
||| general sense.  The Echo record below is one canonical instance
||| (fiber of a map).
public export
Displayed : Type -> Type
Displayed b = b -> Type

-- ============================================================================
-- Echo types as homotopy fibers of a map (canonical construction)
-- ============================================================================

||| The homotopy fiber of `f : A -> B` over `y : B`.
||| A preimage together with a proof it lands at `y`.
public export
record Echo {0 A : Type} {0 B : Type} (f : A -> B) (y : B) where
  constructor MkEcho
  ||| The preimage witness.
  echoPre   : A
  ||| Proof that the witness maps to the target.
  echoProof : f echoPre = y

||| The fiber construction packaged as a displayed type over the codomain.
public export
EchoOf : {0 A, B : Type} -> (A -> B) -> Displayed B
EchoOf f = Echo f

||| Every preimage inhabits the fiber at its image.
public export
echoIntro : {0 A, B : Type} -> (f : A -> B) -> (x : A) -> Echo f (f x)
echoIntro _ x = MkEcho x Refl

-- ============================================================================
-- Slice-category morphisms (HomOver) and functoriality of Echo
-- ============================================================================

||| A morphism in the slice category over B: a map `A -> A'` that commutes
||| with the two projections `f : A -> B` and `f' : A' -> B`.
public export
record HomOver {0 A, A', B : Type} (f : A -> B) (f' : A' -> B) where
  constructor MkHomOver
  ||| The underlying map on total spaces.
  homMap     : A -> A'
  ||| Commutation with the projections.
  homCommute : (x : A) -> f' (homMap x) = f x

||| Identity slice morphism.
public export
idHomOver : {0 A, B : Type} -> (f : A -> B) -> HomOver f f
idHomOver _ = MkHomOver (\x => x) (\_ => Refl)

||| Composition of slice morphisms.  Written `k` after `h`.
public export
compHomOver :
     {0 A, A', A'', B : Type}
  -> {0 f : A -> B} -> {0 f' : A' -> B} -> {0 f'' : A'' -> B}
  -> HomOver f' f''
  -> HomOver f f'
  -> HomOver f f''
compHomOver k h = MkHomOver
  (\x => k.homMap (h.homMap x))
  (\x => trans (k.homCommute (h.homMap x)) (h.homCommute x))

||| Action of a slice morphism on fibers — the functorial map of Echo.
public export
echoMap :
     {0 A, A', B : Type}
  -> {0 f : A -> B} -> {0 f' : A' -> B}
  -> HomOver f f'
  -> {0 y : B}
  -> Echo f y
  -> Echo f' y
echoMap h (MkEcho x p) = MkEcho (h.homMap x) (trans (h.homCommute x) p)

||| Functor law: identity.
public export
echoMapId :
     {0 A, B : Type}
  -> {0 f : A -> B}
  -> {0 y : B}
  -> (e : Echo f y)
  -> echoMap (idHomOver f) e = e
echoMapId (MkEcho _ _) = Refl

||| Functor law: composition.
public export
echoMapCompose :
     {0 A, A', A'', B : Type}
  -> {0 f : A -> B} -> {0 f' : A' -> B} -> {0 f'' : A'' -> B}
  -> (k : HomOver f' f'')
  -> (h : HomOver f f')
  -> {0 y : B}
  -> (e : Echo f y)
  -> echoMap (compHomOver k h) e = echoMap k (echoMap h e)
echoMapCompose k h (MkEcho x p) =
  cong (MkEcho (k.homMap (h.homMap x)))
       (transAssoc (k.homCommute (h.homMap x)) (h.homCommute x) p)

-- ============================================================================
-- Action along a commuting square between different codomains
-- ============================================================================

||| Reindexing / cartesian-lift action: a commuting square
|||
|||         A  ---u-->  A'
|||         |           |
|||         f           f'
|||         v           v
|||         B  ---v-->  B'
|||
||| transports fibers of `f` along `v`.  This is the coherence that
||| crossing-boundary lemmas (multi-module, cross-language ABI) consume.
public export
echoMapSquare :
     {0 A, A', B, B' : Type}
  -> {0 f : A -> B} -> {0 f' : A' -> B'}
  -> (u : A -> A')
  -> (v : B -> B')
  -> (sq : (x : A) -> f' (u x) = v (f x))
  -> {0 y : B}
  -> Echo f y
  -> Echo f' (v y)
echoMapSquare u v sq (MkEcho x p) =
  MkEcho (u x) (trans (sq x) (cong v p))

-- ============================================================================
-- Morphisms of displayed types (cartesian view of HomOver)
-- ============================================================================

||| A morphism of displayed types over a base map `v : B -> B'`: a fibrewise
||| family of functions compatible with `v`.  Every HomOver is a special
||| case of DispHom over the identity base map.
public export
record DispHom
  {0 B, B' : Type}
  (p : Displayed B) (q : Displayed B')
  (v : B -> B') where
  constructor MkDispHom
  dispMap : {0 b : B} -> p b -> q (v b)

||| Identity displayed morphism over the identity base.
public export
idDispHom : {0 B : Type} -> (p : Displayed B) -> DispHom p p (\b => b)
idDispHom _ = MkDispHom (\x => x)

||| A HomOver between two maps into the same codomain induces a DispHom
||| between their fiber displayed-types over the identity on the base.
||| This is the bridge from the slice-morphism view to the fibrational view.
public export
fromHomOver :
     {0 A, A', B : Type}
  -> {0 f : A -> B} -> {0 f' : A' -> B}
  -> HomOver f f'
  -> DispHom (EchoOf f) (EchoOf f') (\b => b)
fromHomOver h = MkDispHom (\e => echoMap h e)
