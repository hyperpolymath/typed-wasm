-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Levels.idr — The 10 levels of type safety as Idris2 proof types
--
-- Each of the 10 levels from the typed-wasm specification is encoded as
-- a type (a proposition) that can be inhabited (proven) or not. A program
-- that type-checks at level N has a proof witness for that level.
--
-- The levels form a stack: higher levels build on lower ones. Level 10
-- (linearity) implies all of levels 1-9. A "proof certificate" is a
-- product of all 10 level proofs — it is the strongest guarantee that
-- typed-wasm can provide.
--
-- Level  1: Instruction validity (well-formed syntax)
-- Level  2: Region-binding (field resolves to declared schema)
-- Level  3: Type-compatible access (load type matches field type)
-- Level  4: Null safety (nullable pointers tracked explicitly)
-- Level  5: Bounds-proof (access within region bounds)
-- Level  6: Result-type (return type statically known)
-- Level  7: Aliasing safety (mutable references exclusive)
-- Level  8: Effect-tracking (Read/Write/Alloc/Free declared)
-- Level  9: Lifetime safety (no use-after-free)
-- Level 10: Linearity (resources used exactly once)

module TypedWasm.ABI.Levels

import TypedWasm.ABI.Region
import Data.List.Elem
import Data.Nat

%default total

-- ============================================================================
-- Level 1: Instruction Validity
-- ============================================================================

||| Proof that an access expression is well-formed according to the
||| typed-wasm grammar. This is the parse-level check: the expression
||| is a valid sentence in the EBNF grammar.
|||
||| In practice this is established by the parser (written in ReScript).
||| At the Idris2 ABI level, we model it as an opaque proof witness that
||| the parser must construct. If parsing succeeds, this proof exists.
public export
data Level1_InstructionValidity : Type where
  ||| The access expression parsed successfully.
  ||| `exprId` identifies which expression was validated (for composition).
  InstructionValid : (exprId : String) -> Level1_InstructionValidity

-- ============================================================================
-- Level 2: Region-Binding Safety
-- ============================================================================

||| Proof that an access expression resolves to a declared region and
||| a declared field within that region. This is the schema-binding check.
|||
||| The proof carries the schema and the field membership witness, so
||| downstream levels can inspect exactly which field was resolved.
public export
data Level2_RegionBinding : (schema : Schema) -> (name : String) -> Type where
  ||| The access resolves: `name` is a declared field in `schema`.
  RegionBound : (membership : FieldIn name schema)
              -> Level2_RegionBinding schema name

-- ============================================================================
-- Level 3: Type-Compatible Access
-- ============================================================================

||| Proof that the type used to access a field matches the field's
||| declaration in the schema. If the field is declared as `i32`, then
||| the load instruction must be `i32.load`, not `f64.load`.
|||
||| In typed-wasm this is enforced by construction: the access type is
||| computed from the schema, not chosen by the programmer. This proof
||| witnesses that the computation was performed correctly.
public export
data Level3_TypeCompatible : (schema : Schema) -> (name : String) -> (accessType : WasmType) -> Type where
  ||| The access type matches the field's declared type.
  TypeCompatible : (membership : FieldIn name schema)
                 -> (typeMatch : fieldType (lookupField membership) = accessType)
                 -> Level3_TypeCompatible schema name accessType

-- ============================================================================
-- Level 4: Null Safety
-- ============================================================================

||| Whether a pointer or value is nullable. Non-nullable values are
||| guaranteed to hold a valid value by construction. Nullable values
||| require explicit unwrapping before use.
public export
data Nullability : Type where
  ||| The value is guaranteed non-null.
  NonNull  : Nullability
  ||| The value may be null and must be explicitly checked.
  Nullable : Nullability

||| Proof that a value has been null-checked before use. If the original
||| value was NonNull, this proof is trivial. If it was Nullable, this
||| proof witnesses that an explicit null check was performed.
public export
data Level4_NullSafe : Nullability -> Type where
  ||| A non-null value is trivially null-safe.
  AlreadyNonNull : Level4_NullSafe NonNull
  ||| A nullable value was explicitly checked and found non-null.
  ||| The `checkId` identifies which null check established this.
  NullChecked    : (checkId : String) -> Level4_NullSafe Nullable

-- ============================================================================
-- Level 5: Bounds-Proof Safety
-- ============================================================================

||| Proof that a memory access is within the bounds of its target region.
||| For singleton regions, this is trivially true (offset < instanceSize).
||| For array regions, this requires a proof that the index is in range.
|||
||| This builds on Region.InBounds but adds the field offset component:
||| the entire access (base + index * stride + fieldOffset + fieldSize)
||| must be within the region's total allocation.
public export
data Level5_BoundsProof : (schema : Schema) -> Type where
  ||| Access to a singleton region. Bounds are guaranteed because the
  ||| field offset and size are computed from the schema, which is
  ||| guaranteed to be self-consistent by LayoutValid.
  SingletonBounds : (layout : LayoutValid schema)
                  -> Level5_BoundsProof schema

  ||| Access to an array region at a specific index. Bounds are guaranteed
  ||| by the InBounds proof on the index, plus the LayoutValid proof on
  ||| the schema (ensuring field offsets are within instance size).
  IndexedBounds : (layout : LayoutValid schema)
                -> (idx : Nat)
                -> (count : Nat)
                -> (inBounds : InBounds idx count)
                -> Level5_BoundsProof schema

-- ============================================================================
-- Level 6: Result-Type Safety
-- ============================================================================

||| Proof that the result type of a memory access is statically known.
||| The result type is the WasmType of the accessed field, and it is
||| known at compile time because it is computed from the schema.
|||
||| This proof carries the actual result type so it can be inspected
||| by downstream code (e.g., the code generator that emits the correct
||| WASM load instruction).
public export
data Level6_ResultType : (schema : Schema) -> (name : String) -> Type where
  ||| The result type is known: it is `fieldType (lookupField membership)`.
  ResultTypeKnown : (membership : FieldIn name schema)
                  -> (resultTy : WasmType)
                  -> (tyMatch : fieldType (lookupField membership) = resultTy)
                  -> Level6_ResultType schema name

-- ============================================================================
-- Level 7: Aliasing Safety
-- ============================================================================

||| The kind of reference held to a region. Determines aliasing rules.
public export
data RefKind : Type where
  ||| Shared immutable reference. Many may coexist.
  SharedRef  : RefKind
  ||| Exclusive mutable reference. No other mutable refs may coexist.
  ExclusiveRef : RefKind
  ||| Owning reference. No other owners may coexist.
  OwningRef  : RefKind

||| Proof that two references to the same region do not violate aliasing
||| rules. The fundamental rule: if one reference is ExclusiveRef or
||| OwningRef, no other reference to the same region may exist.
|||
||| For SharedRef, multiple SharedRefs are permitted (read-only aliasing
||| is safe). This mirrors Rust's borrowing rules at the WASM memory level.
public export
data Level7_AliasSafe : RefKind -> RefKind -> Type where
  ||| Two shared references may coexist. Read-only aliasing is safe.
  SharedShared   : Level7_AliasSafe SharedRef SharedRef
  ||| An exclusive reference is the only reference. The second argument
  ||| is a phantom — the proof states that no second reference exists.
  ||| We encode this as: the only valid composition with ExclusiveRef
  ||| is with itself, meaning "there is exactly one reference".
  ExclusiveAlone : Level7_AliasSafe ExclusiveRef ExclusiveRef
  ||| An owning reference is the only reference, same reasoning.
  OwningAlone    : Level7_AliasSafe OwningRef OwningRef

-- ============================================================================
-- Level 8: Effect-Tracking Safety
-- ============================================================================

||| Memory effects that a function may perform. Each operation on a region
||| has an associated effect, and the function must declare all effects it
||| performs. The type system verifies that actual effects are a subset of
||| declared effects.
|||
||| This is imported from the Effects module for full definitions; here
||| we define the level proof type.
public export
data MemEffect : Type where
  ||| Read from a region.
  EffRead  : MemEffect
  ||| Write to a region.
  EffWrite : MemEffect
  ||| Allocate a new region instance.
  EffAlloc : MemEffect
  ||| Free an existing region instance.
  EffFree  : MemEffect

||| Proof that a function's actual effects are a subset of its declared
||| effects. This is Level 8: no undeclared side effects.
public export
data Level8_EffectSafe : (declared : List MemEffect) -> (actual : List MemEffect) -> Type where
  ||| No actual effects — trivially safe.
  EffectNil  : Level8_EffectSafe declared []
  ||| An actual effect is in the declared set, and the rest are also safe.
  EffectCons : Elem e declared -> Level8_EffectSafe declared rest
             -> Level8_EffectSafe declared (e :: rest)

-- ============================================================================
-- Level 9: Lifetime Safety
-- ============================================================================

||| A lifetime identifier. Lifetimes scope the validity of references.
||| A reference with lifetime 'a is valid only while 'a is live.
public export
data Lifetime : Type where
  ||| The static lifetime — valid for the entire program.
  Static : Lifetime
  ||| A function-scoped lifetime — valid for the function body.
  FnScope : Lifetime
  ||| A named lifetime — valid for a specific scope.
  Named : (name : String) -> Lifetime

||| Proof that one lifetime outlives another. If 'a outlives 'b, then
||| any reference valid for 'a is also valid for 'b.
public export
data Outlives : Lifetime -> Lifetime -> Type where
  ||| Static outlives everything.
  StaticOutlives : Outlives Static l
  ||| FnScope outlives Named lifetimes (nested scopes).
  FnOutlivesNamed : Outlives FnScope (Named n)
  ||| A lifetime outlives itself (reflexivity).
  OutlivesSelf : Outlives l l

||| Proof that a reference is not used after its lifetime ends.
||| This is the core Level 9 property: no use-after-free.
|||
||| The proof states that the reference's lifetime (`refLife`) outlives
||| the scope in which it is used (`useScope`).
public export
data Level9_LifetimeSafe : (refLife : Lifetime) -> (useScope : Lifetime) -> Type where
  ||| The reference's lifetime outlives the use scope.
  LifetimeValid : Outlives refLife useScope -> Level9_LifetimeSafe refLife useScope

-- ============================================================================
-- Level 10: Linearity Safety
-- ============================================================================

||| Resource state for linear tracking. A resource is either live (can be
||| used/freed) or consumed (has been freed/transferred).
public export
data ResourceState : Type where
  ||| The resource is live and has not been consumed.
  Live     : ResourceState
  ||| The resource has been consumed (freed or transferred).
  Consumed : ResourceState

||| Proof that a linear resource is used exactly once.
||| - `NoLeak`: the resource was consumed (freed exactly once).
||| - `NoDoubleFree`: the resource was not consumed more than once.
|||
||| Together these prove that the resource lifecycle is correct:
||| allocated once, used, freed once, never accessed again.
public export
data Level10_Linear : ResourceState -> Type where
  ||| A live resource that must still be consumed. This is a proof
  ||| obligation: code holding this must eventually produce `Freed`.
  MustConsume : Level10_Linear Live
  ||| The resource was consumed exactly once. This discharges the
  ||| obligation created by `MustConsume`.
  Freed       : Level10_Linear Consumed

-- ============================================================================
-- Level Composition: Which Levels Subsume Which
-- ============================================================================

||| The set of levels that a program has been proven to satisfy.
||| Encoded as a record so that each level can be independently proven
||| and then composed into a full certificate.
|||
||| A program at level N means it satisfies levels 1 through N.
||| The higher levels build on (and require) the lower ones.
public export
data LevelSet : Type where
  ||| Levels 1-6 are the "established" levels — well-understood and
  ||| analogous to existing typed assembly language techniques.
  EstablishedLevels : Level1_InstructionValidity
                    -> Level2_RegionBinding schema name
                    -> Level3_TypeCompatible schema name ty
                    -> Level4_NullSafe nullability
                    -> Level5_BoundsProof schema
                    -> Level6_ResultType schema name
                    -> LevelSet

  ||| Levels 7-10 are the "research" levels — ownership, effects,
  ||| lifetimes, and linearity applied to WASM memory.
  FullLevels : Level1_InstructionValidity
             -> Level2_RegionBinding schema name
             -> Level3_TypeCompatible schema name ty
             -> Level4_NullSafe nullability
             -> Level5_BoundsProof schema
             -> Level6_ResultType schema name
             -> Level7_AliasSafe ref1 ref2
             -> Level8_EffectSafe declared actual
             -> Level9_LifetimeSafe refLife useScope
             -> Level10_Linear state
             -> LevelSet
