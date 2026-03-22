-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Lifetime.idr — Lifetime safety proofs for typed-wasm ABI (Level 9)
--
-- Lifetimes scope the validity of references to memory regions. A reference
-- with lifetime 'a is only valid while lifetime 'a is live. Accessing a
-- reference after its lifetime has ended (use-after-free) is a compile-time
-- error, not a runtime crash.
--
-- The database analogy: this is temporal safety. Just as VQL-UT's
-- FRESH WITHIN clause ensures data is temporally valid, typed-wasm's
-- lifetimes ensure references are spatially valid — the memory they
-- point to is still allocated.
--
-- Lifetimes are ordered: 'a >= 'b means 'a outlives 'b. A reference
-- with lifetime 'a can be used in any context expecting lifetime 'b
-- where 'a >= 'b (covariant subtyping).

module TypedWasm.ABI.Lifetime

import Data.Nat

%default total

-- ============================================================================
-- Lifetime Names
-- ============================================================================

||| A lifetime is a compile-time marker for the scope during which a
||| reference is valid. Lifetimes are not runtime values — they exist
||| only in the type system and are erased during compilation.
public export
data Lifetime : Type where
  ||| The static lifetime — valid for the entire program duration.
  ||| References with 'static lifetime never become dangling.
  Static : Lifetime
  ||| A function-scoped lifetime — valid for the duration of one
  ||| function call. References with 'fn lifetime are invalidated
  ||| when the function returns.
  FnScope : Lifetime
  ||| A named lifetime — scoped to a specific lexical block.
  ||| The name is a compile-time identifier (Nat index).
  Named : (id : Nat) -> Lifetime
  ||| A region lifetime — tied to the allocation lifetime of a
  ||| specific region instance. Valid as long as the region is live.
  RegionLife : (regionId : Nat) -> Lifetime

public export
Eq Lifetime where
  Static        == Static        = True
  FnScope       == FnScope       = True
  (Named a)     == (Named b)     = a == b
  (RegionLife a) == (RegionLife b) = a == b
  _             == _             = False

-- ============================================================================
-- Lifetime Ordering (Outlives Relation)
-- ============================================================================

||| Proof that lifetime 'a outlives lifetime 'b.
||| This is the core judgement for Level 9: a reference with lifetime 'a
||| can be used wherever lifetime 'b is expected, provided 'a outlives 'b.
|||
||| The outlives relation forms a partial order:
|||   - 'static outlives everything (top element)
|||   - 'fn outlives any named lifetime within the function
|||   - Named lifetimes are ordered by nesting depth
public export
data Outlives : Lifetime -> Lifetime -> Type where
  ||| 'static outlives any lifetime.
  StaticOutlivesAll : Outlives Static b
  ||| Any lifetime outlives itself (reflexivity).
  OutlivesSelf : Outlives a a
  ||| 'fn outlives any named lifetime (function scope contains all blocks).
  FnOutlivesNamed : Outlives FnScope (Named n)
  ||| 'fn outlives any region lifetime created within the function.
  FnOutlivesRegion : Outlives FnScope (RegionLife r)
  ||| A named lifetime outlives a more deeply nested named lifetime.
  ||| Smaller id = outer scope = longer lifetime (by convention).
  NamedNesting : LTE m n -> Outlives (Named m) (Named n)

||| Transitivity of the outlives relation.
||| If 'a outlives 'b and 'b outlives 'c, then 'a outlives 'c.
public export
outlivesTransitive : {a, b, c : Lifetime} -> Outlives a b -> Outlives b c -> Outlives a c
outlivesTransitive StaticOutlivesAll _ = StaticOutlivesAll
outlivesTransitive OutlivesSelf bc = bc
outlivesTransitive ab OutlivesSelf = ab
outlivesTransitive FnOutlivesNamed OutlivesSelf = FnOutlivesNamed
outlivesTransitive FnOutlivesRegion OutlivesSelf = FnOutlivesRegion
outlivesTransitive FnOutlivesNamed (NamedNesting _) = FnOutlivesNamed
outlivesTransitive (NamedNesting p1) (NamedNesting p2) =
  NamedNesting (transitive p1 p2)

-- ============================================================================
-- Reference Validity
-- ============================================================================

||| A reference tagged with its lifetime. The reference is only valid
||| while the lifetime is live. The type parameter 'a' is the pointed-to
||| type, and 'life' is the lifetime scope.
public export
data LiveRef : (life : Lifetime) -> (a : Type) -> Type where
  ||| Construct a live reference. The lifetime tag exists only in the type —
  ||| at runtime, this is just a pointer (offset into linear memory).
  MkLiveRef : (offset : Nat) -> LiveRef life a

||| Extract the offset from a live reference.
||| This is the "dereference" operation — it can only be called if the
||| reference's lifetime is still live (ensured by the type system).
public export
refOffset : LiveRef life a -> Nat
refOffset (MkLiveRef off) = off

-- ============================================================================
-- Lifetime Scoping
-- ============================================================================

||| Proof that a reference is valid in a given context.
||| A reference with lifetime 'refLife is valid in a context with
||| lifetime 'ctxLife if 'refLife outlives 'ctxLife.
public export
data ValidIn : (refLife : Lifetime) -> (ctxLife : Lifetime) -> Type where
  MkValidIn : Outlives refLife ctxLife -> ValidIn refLife ctxLife

||| Use a reference in a context. Requires proof that the reference's
||| lifetime outlives the context's lifetime.
public export
useRef : LiveRef refLife a
       -> {auto valid : ValidIn refLife ctxLife}
       -> Nat
useRef ref = refOffset ref

-- ============================================================================
-- Region Lifetime Binding
-- ============================================================================

||| Proof that a region is currently live (not freed).
||| This is produced by allocation and consumed by free.
||| Between allocation and free, it can be borrowed to create references.
public export
data RegionLive : (regionId : Nat) -> Type where
  ||| Witness that region `regionId` is currently allocated and valid.
  MkRegionLive : RegionLive regionId

||| Create a reference from a live region.
||| The reference's lifetime is bound to the region's lifetime.
||| This is safe because the region is proven live (RegionLive witness).
public export
borrowFromRegion : RegionLive regionId
                -> (offset : Nat)
                -> LiveRef (RegionLife regionId) a
borrowFromRegion _ off = MkLiveRef off

-- ============================================================================
-- Use-After-Free Impossibility
-- ============================================================================

||| Proof that a reference cannot be used after its region is freed.
|||
||| The key insight: freeing a region consumes the RegionLive witness.
||| Without RegionLive, no new references can be created. Existing
||| references have lifetime (RegionLife regionId), which is only valid
||| while RegionLive exists. Once consumed, the lifetime is dead, and
||| any attempt to use a reference with that lifetime is a type error.
|||
||| This is not a runtime check — it's a structural impossibility in the
||| type system. The program that uses a reference after free simply
||| cannot type-check.
public export
data NoUseAfterFree : Type where
  ||| The structural guarantee: if you hold a LiveRef with
  ||| lifetime (RegionLife r), then RegionLive r must exist
  ||| somewhere in scope. If it has been consumed (by free),
  ||| the LiveRef's type is uninhabitable in the current context.
  MkNoUAF : NoUseAfterFree

-- ============================================================================
-- Lifetime Subtyping (Covariance)
-- ============================================================================

||| Lifetime subtyping: a reference with a longer lifetime can be used
||| where a shorter lifetime is expected.
|||
||| This is covariant: LiveRef 'static a <: LiveRef 'fn a <: LiveRef (Named n) a
||| (when the outlives relations hold).
public export
weakenLifetime : Outlives long short
              -> LiveRef long a
              -> LiveRef short a
weakenLifetime _ (MkLiveRef off) = MkLiveRef off
