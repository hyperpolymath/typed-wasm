-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- src/abi/layout/Types.idr
--
-- Cross-language WasmGC type layout contracts (aggregate library role).
--
-- This module belongs to the SECONDARY purpose of typed-wasm: the aggregate
-- library that provides formally verified type layout and ABI conventions for
-- languages that compile to typed WebAssembly.  The PRIMARY purpose (TypeLL
-- type safety for WasmGC linear memory) lives in TypedWasm/ABI/.
--
-- ADR-004 documents both roles.  These two subtrees are intentionally
-- separated so that the 10-level WASM memory safety proofs and the
-- cross-language layout contracts are developed and reviewed independently.
--
-- Consumer languages:
--   - nextgen-languages/affinescript  (affine type discipline)
--   - nextgen-languages/ephapax       (dyadic linear/affine)
--
-- Pipeline position:  katagoria → typell → typed-wasm → PanLL
--                                                ↑
--                                    this module lives here

module Layout.Types

import Decidable.Equality
import Data.List

%default total

-- ─────────────────────────────────────────────────────────────────────────────
-- Fundamental WasmGC layout contracts
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Each type below specifies what the agreed WasmGC encoding is.
-- Proofs follow the data definitions:
--   * DecEq instances for all three types (required by layout-equality proofs)
--   * Nullability witnesses for Option and String layouts
--   * Distinctness: stringLayout ≠ optionLayout, resultLayout ≠ optionLayout
--
-- %default total enforced. No partial proofs, no totality bypasses, no coercions.

-- | The shared WasmGC primitive types agreed between all consumer languages.
public export
data WasmPrimitive
  = WasmI32             -- Int, Bool (0 = false, 1 = true)
  | WasmI64             -- Int64
  | WasmF32             -- Float32
  | WasmF64             -- Float (default Float in source languages)
  | WasmFuncRef         -- Function reference

-- | A WasmGC heap type.  References are always typed in WasmGC.
--
-- Recursive types (WHT_Var / WHT_Rec) use de Bruijn indices:
--   WHT_Var 0  — refers to the immediately enclosing WHT_Rec binder
--   WHT_Var 1  — refers to the second-enclosing WHT_Rec binder, etc.
--   WHT_Rec body — introduces μ; every WHT_Var 0 in `body` refers to this node
--
-- Example: List elem =
--   WHT_Rec (WHT_Struct [("head", WVT_Ref elem), ("tail", WVT_RefNull (WHT_Var 0))])
-- which is the WasmGC type  μX. (struct (field (ref elem)) (field (ref null X)))
--
-- WHT_Any is the WasmGC top reference type (`any` in the spec).  All struct,
-- array, and i31 references are subtypes of `any`.  It is used as the payload
-- type in `resultLayout` (a `Result T E` stores its payload as `(ref any)` and
-- casts to the concrete T or E at the use site).
--
-- `WasmHeapType` and `WasmValType` are mutually recursive: the former contains
-- the latter in WHT_Array / WHT_Struct / WHT_Func, and the latter contains the
-- former in WVT_Ref / WVT_RefNull.  Both declarations must live in a single
-- `mutual` block so each name is in scope for the other.
mutual
  public export
  data WasmHeapType
    = WHT_Array WasmValType                       -- (array <valtype>)
    | WHT_Struct (List (String, WasmValType))      -- (struct (field ...))
    | WHT_Func (List WasmValType) (List WasmValType)  -- (func (param ...) (result ...))
    | WHT_Var Nat                                  -- bound type variable (de Bruijn index)
    | WHT_Rec WasmHeapType                         -- μ-binder: (rec <heaptype>)
    | WHT_Any                                      -- top reference type: (any)

  -- | A WasmGC value type — either a primitive or a typed reference.
  public export
  data WasmValType
    = WVT_Prim WasmPrimitive
    | WVT_Ref WasmHeapType          -- (ref <heaptype>)   — non-nullable
    | WVT_RefNull WasmHeapType      -- (ref null <heaptype>) — nullable

-- ─────────────────────────────────────────────────────────────────────────────
-- Agreed layouts for standard source-language types
-- ─────────────────────────────────────────────────────────────────────────────

||| The agreed WasmGC layout for `String` in all consumer languages.
||| Encoding: (ref (array i8)) — a UTF-8 byte array.
||| Both AffineScript and Ephapax must use this layout.
|||
||| `public export` is required so that downstream `Refl`-based distinctness
||| proofs (e.g. stringOptionDistinct) reduce at unification time.
public export
stringLayout : WasmValType
stringLayout = WVT_Ref (WHT_Array (WVT_Prim WasmI32))
-- Note: i8 is represented as i32 in WasmGC value positions.

||| The agreed layout for `Option T` (nullable reference).
||| Encoding: (ref null T) — WasmGC native nullable reference.
||| T must itself be a heap type (structs, arrays, funcs).
public export
optionLayout : WasmHeapType -> WasmValType
optionLayout t = WVT_RefNull t

||| The agreed layout for `Result T E` (tagged union).
||| Encoding: (ref (struct (field i32) (field (ref any))))
||| Field 0: discriminant (0 = Ok, 1 = Err).
||| Field 1: payload as (ref any) — cast to concrete T or E at use site.
public export
resultLayout : WasmValType
resultLayout =
  WVT_Ref (WHT_Struct [("tag", WVT_Prim WasmI32), ("payload", WVT_Ref WHT_Any)])
-- Payload is (ref any): the concrete T or E is recovered by a checked downcast
-- at the use site.  WHT_Any is the WasmGC top reference type — all structs and
-- arrays are subtypes, so this is the canonical encoding for a sum-type payload.

||| The agreed layout for an arbitrary Record (product type).
||| Encoding: (ref (struct (field T1) (field T2) ... (field Tn)))
||| Fields are ordered as they appear in the source language declaration.
public export
recordLayout : List (String, WasmValType) -> WasmValType
recordLayout fields = WVT_Ref (WHT_Struct fields)

||| The agreed layout for an arbitrary Enum (sum type).
||| Encoding: (ref (struct (field i32) (field (ref any))))
||| Field 0: tag (discriminant).
||| Field 1: payload as (ref any).
|||
||| This is the generalized version of `resultLayout`.
public export
enumLayout : WasmValType
enumLayout = WVT_Ref (WHT_Struct [("tag", WVT_Prim WasmI32), ("payload", WVT_Ref WHT_Any)])

-- ─────────────────────────────────────────────────────────────────────────────
-- DecEq instances
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Required by the layout-equality proofs below and by any downstream code
-- that needs to compare types at the boundary.

public export
DecEq WasmPrimitive where
  decEq WasmI32    WasmI32    = Yes Refl
  decEq WasmI64    WasmI64    = Yes Refl
  decEq WasmF32    WasmF32    = Yes Refl
  decEq WasmF64    WasmF64    = Yes Refl
  decEq WasmFuncRef WasmFuncRef = Yes Refl
  -- distinct constructors — No proofs by absurd case analysis
  decEq WasmI32 WasmI64    = No (\case Refl impossible)
  decEq WasmI32 WasmF32    = No (\case Refl impossible)
  decEq WasmI32 WasmF64    = No (\case Refl impossible)
  decEq WasmI32 WasmFuncRef = No (\case Refl impossible)
  decEq WasmI64 WasmI32    = No (\case Refl impossible)
  decEq WasmI64 WasmF32    = No (\case Refl impossible)
  decEq WasmI64 WasmF64    = No (\case Refl impossible)
  decEq WasmI64 WasmFuncRef = No (\case Refl impossible)
  decEq WasmF32 WasmI32    = No (\case Refl impossible)
  decEq WasmF32 WasmI64    = No (\case Refl impossible)
  decEq WasmF32 WasmF64    = No (\case Refl impossible)
  decEq WasmF32 WasmFuncRef = No (\case Refl impossible)
  decEq WasmF64 WasmI32    = No (\case Refl impossible)
  decEq WasmF64 WasmI64    = No (\case Refl impossible)
  decEq WasmF64 WasmF32    = No (\case Refl impossible)
  decEq WasmF64 WasmFuncRef = No (\case Refl impossible)
  decEq WasmFuncRef WasmI32  = No (\case Refl impossible)
  decEq WasmFuncRef WasmI64  = No (\case Refl impossible)
  decEq WasmFuncRef WasmF32  = No (\case Refl impossible)
  decEq WasmFuncRef WasmF64  = No (\case Refl impossible)

-- `WHT_Struct` fields are `List (String, WasmValType)`.
-- `DecEq String` is in Prelude; `DecEq (List a)` is in Prelude given `DecEq a`.
-- `DecEq (a, b)` is NOT in Prelude in all Idris2 versions, so we provide it here.
-- This instance must be declared BEFORE the mutual block so it is in scope when
-- `decEq xs ys` is resolved inside the `WHT_Struct` case.

-- Rewritten as case-of instead of nested `with`: Idris2 0.8's with-block pattern
-- unification produces `x1 unifies with ?x2` warnings in nested position.  Plain
-- `case` avoids the with-block elaboration path entirely.
public export
DecEq a => DecEq b => DecEq (a, b) where
  decEq (x1, y1) (x2, y2) = case decEq x1 x2 of
    No  neq  => No (\case Refl => neq Refl)
    Yes Refl => case decEq y1 y2 of
      Yes Refl => Yes Refl
      No  neq  => No (\case Refl => neq Refl)

-- ─── Decidable equality for WasmHeapType / WasmValType ─────────────────────
--
-- The two types are mutually recursive and the WHT_Struct constructor carries
-- `List (String, WasmValType)`.  Idris2 0.8's interface-resolution chain
-- through `DecEq WasmValType` → `DecEq (String, WasmValType)` →
-- `DecEq (List (String, WasmValType))` fails inside a mutual instance block
-- (the interface for `WasmValType` is not yet resolved when `WHT_Struct`
-- needs it).
--
-- Workaround: declare explicit mutual plain functions
-- (`decEqHT` / `decEqVT` / `decEqFields` / `decEqVTList`), then expose them
-- through thin non-mutual `DecEq` instance wrappers.  This sidesteps
-- interface-resolution dispatch — the helpers call each other directly by
-- name, which works inside `mutual`.

mutual
  ||| Decidable equality for WasmHeapType, as a plain function.
  public export
  decEqHT : (a, b : WasmHeapType) -> Dec (a = b)
  -- ── Same-constructor cases ─────────────────────────────────────────────
  decEqHT (WHT_Array a) (WHT_Array b) = case decEqVT a b of
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqHT (WHT_Struct xs) (WHT_Struct ys) = case decEqFields xs ys of
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqHT (WHT_Func ps1 rs1) (WHT_Func ps2 rs2) = case decEqVTList ps1 ps2 of
    No  neq  => No (\case Refl => neq Refl)
    Yes Refl => case decEqVTList rs1 rs2 of
      Yes Refl => Yes Refl
      No  neq  => No (\case Refl => neq Refl)
  decEqHT (WHT_Var m) (WHT_Var n) = case decEq m n of
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqHT (WHT_Rec h1) (WHT_Rec h2) = case decEqHT h1 h2 of
    -- Structurally recursive: h1/h2 are strict subterms of WHT_Rec h1/h2.
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqHT WHT_Any WHT_Any = Yes Refl
  -- ── Cross-constructor cases (all absurd) ───────────────────────────────
  decEqHT (WHT_Array _)  (WHT_Struct _) = No (\case Refl impossible)
  decEqHT (WHT_Array _)  (WHT_Func _ _) = No (\case Refl impossible)
  decEqHT (WHT_Array _)  (WHT_Var _)    = No (\case Refl impossible)
  decEqHT (WHT_Array _)  (WHT_Rec _)    = No (\case Refl impossible)
  decEqHT (WHT_Array _)  WHT_Any        = No (\case Refl impossible)
  decEqHT (WHT_Struct _) (WHT_Array _)  = No (\case Refl impossible)
  decEqHT (WHT_Struct _) (WHT_Func _ _) = No (\case Refl impossible)
  decEqHT (WHT_Struct _) (WHT_Var _)    = No (\case Refl impossible)
  decEqHT (WHT_Struct _) (WHT_Rec _)    = No (\case Refl impossible)
  decEqHT (WHT_Struct _) WHT_Any        = No (\case Refl impossible)
  decEqHT (WHT_Func _ _) (WHT_Array _)  = No (\case Refl impossible)
  decEqHT (WHT_Func _ _) (WHT_Struct _) = No (\case Refl impossible)
  decEqHT (WHT_Func _ _) (WHT_Var _)    = No (\case Refl impossible)
  decEqHT (WHT_Func _ _) (WHT_Rec _)    = No (\case Refl impossible)
  decEqHT (WHT_Func _ _) WHT_Any        = No (\case Refl impossible)
  decEqHT (WHT_Var _)    (WHT_Array _)  = No (\case Refl impossible)
  decEqHT (WHT_Var _)    (WHT_Struct _) = No (\case Refl impossible)
  decEqHT (WHT_Var _)    (WHT_Func _ _) = No (\case Refl impossible)
  decEqHT (WHT_Var _)    (WHT_Rec _)    = No (\case Refl impossible)
  decEqHT (WHT_Var _)    WHT_Any        = No (\case Refl impossible)
  decEqHT (WHT_Rec _)    (WHT_Array _)  = No (\case Refl impossible)
  decEqHT (WHT_Rec _)    (WHT_Struct _) = No (\case Refl impossible)
  decEqHT (WHT_Rec _)    (WHT_Func _ _) = No (\case Refl impossible)
  decEqHT (WHT_Rec _)    (WHT_Var _)    = No (\case Refl impossible)
  decEqHT (WHT_Rec _)    WHT_Any        = No (\case Refl impossible)
  decEqHT WHT_Any        (WHT_Array _)  = No (\case Refl impossible)
  decEqHT WHT_Any        (WHT_Struct _) = No (\case Refl impossible)
  decEqHT WHT_Any        (WHT_Func _ _) = No (\case Refl impossible)
  decEqHT WHT_Any        (WHT_Var _)    = No (\case Refl impossible)
  decEqHT WHT_Any        (WHT_Rec _)    = No (\case Refl impossible)

  ||| Decidable equality for WasmValType, as a plain function.
  public export
  decEqVT : (a, b : WasmValType) -> Dec (a = b)
  decEqVT (WVT_Prim p1) (WVT_Prim p2) = case decEq p1 p2 of
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqVT (WVT_Ref h1) (WVT_Ref h2) = case decEqHT h1 h2 of
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqVT (WVT_RefNull h1) (WVT_RefNull h2) = case decEqHT h1 h2 of
    Yes Refl => Yes Refl
    No  neq  => No (\case Refl => neq Refl)
  decEqVT (WVT_Prim _)    (WVT_Ref _)     = No (\case Refl impossible)
  decEqVT (WVT_Prim _)    (WVT_RefNull _) = No (\case Refl impossible)
  decEqVT (WVT_Ref _)     (WVT_Prim _)    = No (\case Refl impossible)
  decEqVT (WVT_Ref _)     (WVT_RefNull _) = No (\case Refl impossible)
  decEqVT (WVT_RefNull _) (WVT_Prim _)    = No (\case Refl impossible)
  decEqVT (WVT_RefNull _) (WVT_Ref _)     = No (\case Refl impossible)

  ||| Decidable equality for a list of WasmValType — needed by WHT_Func.
  public export
  decEqVTList : (xs, ys : List WasmValType) -> Dec (xs = ys)
  decEqVTList [] []             = Yes Refl
  decEqVTList [] (_ :: _)       = No (\case Refl impossible)
  decEqVTList (_ :: _) []       = No (\case Refl impossible)
  decEqVTList (x :: xs) (y :: ys) = case decEqVT x y of
    No  neq  => No (\case Refl => neq Refl)
    Yes Refl => case decEqVTList xs ys of
      Yes Refl => Yes Refl
      No  neq  => No (\case Refl => neq Refl)

  ||| Decidable equality for struct field lists — needed by WHT_Struct.
  public export
  decEqFields : (xs, ys : List (String, WasmValType)) -> Dec (xs = ys)
  decEqFields [] []             = Yes Refl
  decEqFields [] (_ :: _)       = No (\case Refl impossible)
  decEqFields (_ :: _) []       = No (\case Refl impossible)
  decEqFields ((s1, v1) :: xs) ((s2, v2) :: ys) = case decEq s1 s2 of
    No  neq  => No (\case Refl => neq Refl)
    Yes Refl => case decEqVT v1 v2 of
      No  neq  => No (\case Refl => neq Refl)
      Yes Refl => case decEqFields xs ys of
        Yes Refl => Yes Refl
        No  neq  => No (\case Refl => neq Refl)

-- Thin `DecEq` interface wrappers — now that the mutual dispatch is handled
-- by the plain functions above, the interface instances are one-liners.

public export
DecEq WasmHeapType where
  decEq = decEqHT

public export
DecEq WasmValType where
  decEq = decEqVT

-- ─────────────────────────────────────────────────────────────────────────────
-- Nullability witnesses
-- ─────────────────────────────────────────────────────────────────────────────

||| A proof that a WasmValType is non-nullable (uses WVT_Ref, not WVT_RefNull).
public export
data IsNonNull : WasmValType -> Type where
  RefIsNonNull : IsNonNull (WVT_Ref h)

||| A proof that a WasmValType is nullable (uses WVT_RefNull).
public export
data IsNullable : WasmValType -> Type where
  RefNullIsNullable : IsNullable (WVT_RefNull h)

||| `stringLayout` is non-nullable.
||| String references must always be valid (null is not a String).
|||
||| Lowercase identifiers in Idris2 type signatures are auto-bound as implicit
||| arguments, which would shadow the real `stringLayout`.  Fully qualifying as
||| `Layout.Types.stringLayout` prevents the auto-bind and causes the function
||| body (which is `public export`) to reduce at unification.
public export
stringLayoutNonNull : IsNonNull Layout.Types.stringLayout
stringLayoutNonNull = RefIsNonNull

||| `optionLayout t` is always nullable.
||| This is the semantic intent: Option T = the possibility of nothing.
public export
optionLayoutNullable : (t : WasmHeapType) -> IsNullable (Layout.Types.optionLayout t)
optionLayoutNullable _ = RefNullIsNullable

||| `resultLayout` is non-nullable.
||| Results are always present — the Ok/Err distinction is in the tag field.
public export
resultLayoutNonNull : IsNonNull Layout.Types.resultLayout
resultLayoutNonNull = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Distinctness proofs
-- ─────────────────────────────────────────────────────────────────────────────

||| String and Option layouts are distinct: String is non-null; Option is nullable.
||| This prevents any code from confusing `String` with `Option String`.
|||
||| Fully qualify both layouts in the type signature so Idris2 does not auto-bind
||| them as implicit pattern variables.  With the qualified names, `stringLayout`
||| reduces to `WVT_Ref ...` and `optionLayout t` reduces to `WVT_RefNull t`; the
||| resulting equality `WVT_Ref ... = WVT_RefNull ...` is absurd by constructor
||| mismatch.
public export
stringOptionDistinct : (t : WasmHeapType)
                    -> Layout.Types.stringLayout = Layout.Types.optionLayout t
                    -> Void
stringOptionDistinct _ prf = case prf of Refl impossible

||| Primitives are not heap references.
||| Protects against accidentally encoding a primitive as a reference type.
public export
primNotRef : (p : WasmPrimitive) -> (h : WasmHeapType) -> WVT_Prim p = WVT_Ref h -> Void
primNotRef _ _ prf = case prf of Refl impossible

||| Primitives are not nullable references either.
public export
primNotRefNull : (p : WasmPrimitive) -> (h : WasmHeapType) -> WVT_Prim p = WVT_RefNull h -> Void
primNotRefNull _ _ prf = case prf of Refl impossible

-- ─────────────────────────────────────────────────────────────────────────────
-- Recursive type distinctness
-- ─────────────────────────────────────────────────────────────────────────────

||| A recursive binder is never a plain array type.
public export
recNotArray : (h : WasmHeapType) -> (v : WasmValType) -> WHT_Rec h = WHT_Array v -> Void
recNotArray _ _ prf = case prf of Refl impossible

||| A recursive binder is never a struct type.
public export
recNotStruct : (h : WasmHeapType) -> (fs : List (String, WasmValType)) -> WHT_Rec h = WHT_Struct fs -> Void
recNotStruct _ _ prf = case prf of Refl impossible

||| A bound variable is never a struct type.
public export
varNotStruct : (n : Nat) -> (fs : List (String, WasmValType)) -> WHT_Var n = WHT_Struct fs -> Void
varNotStruct _ _ prf = case prf of Refl impossible

||| A bound variable is never a recursive binder.
public export
varNotRec : (n : Nat) -> (h : WasmHeapType) -> WHT_Var n = WHT_Rec h -> Void
varNotRec _ _ prf = case prf of Refl impossible

||| WHT_Var is injective: equal indices give equal variables.
public export
varInjective : (m, n : Nat) -> WHT_Var m = WHT_Var n -> m = n
varInjective _ _ Refl = Refl

||| WHT_Rec is injective: equal bodies give equal recursive types.
public export
recInjective : (h1, h2 : WasmHeapType) -> WHT_Rec h1 = WHT_Rec h2 -> h1 = h2
recInjective _ _ Refl = Refl

||| WHT_Any is not an array, struct, func, var, or recursive type.
||| Prevents any code from treating the top type as a concrete layout.
public export
anyNotArray  : (v : WasmValType) -> WHT_Any = WHT_Array v -> Void
anyNotArray  _ prf = case prf of Refl impossible

public export
anyNotStruct : (fs : List (String, WasmValType)) -> WHT_Any = WHT_Struct fs -> Void
anyNotStruct _ prf = case prf of Refl impossible

public export
anyNotFunc   : (ps, rs : List WasmValType) -> WHT_Any = WHT_Func ps rs -> Void
anyNotFunc   _ _ prf = case prf of Refl impossible

public export
anyNotVar    : (n : Nat) -> WHT_Any = WHT_Var n -> Void
anyNotVar    _ prf = case prf of Refl impossible

public export
anyNotRec    : (h : WasmHeapType) -> WHT_Any = WHT_Rec h -> Void
anyNotRec    _ prf = case prf of Refl impossible

||| `resultLayout` payload uses (ref any): correct WasmGC encoding.
public export
resultPayloadIsAny
    : Layout.Types.resultLayout = WVT_Ref (WHT_Struct [("tag", WVT_Prim WasmI32), ("payload", WVT_Ref WHT_Any)])
resultPayloadIsAny = Refl
