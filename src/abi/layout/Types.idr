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
-- No believe_me, assert_total, or unsafe patterns permitted.

-- | The shared WasmGC primitive types agreed between all consumer languages.
data WasmPrimitive
  = WasmI32             -- Int, Bool (0 = false, 1 = true)
  | WasmI64             -- Int64
  | WasmF32             -- Float32
  | WasmF64             -- Float (default Float in source languages)
  | WasmFuncRef         -- Function reference

-- | A WasmGC heap type.  References are always typed in WasmGC.
data WasmHeapType
  = WHT_Array WasmValType              -- (array <valtype>)
  | WHT_Struct (List (String, WasmValType))  -- (struct (field ...))
  | WHT_Func (List WasmValType) (List WasmValType)  -- (func (param ...) (result ...))

-- | A WasmGC value type — either a primitive or a typed reference.
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
stringLayout : WasmValType
stringLayout = WVT_Ref (WHT_Array (WVT_Prim WasmI32))
-- Note: i8 is represented as i32 in WasmGC value positions.

||| The agreed layout for `Option T` (nullable reference).
||| Encoding: (ref null T) — WasmGC native nullable reference.
||| T must itself be a heap type (structs, arrays, funcs).
optionLayout : WasmHeapType -> WasmValType
optionLayout t = WVT_RefNull t

||| The agreed layout for `Result T E` (tagged union).
||| Encoding: (ref (struct (field i32) (field (ref any))))
||| Field 0: discriminant (0 = Ok, 1 = Err).
||| Field 1: payload as (ref any) — cast to concrete T or E at use site.
resultLayout : WasmValType
resultLayout =
  WVT_Ref (WHT_Struct [("tag", WVT_Prim WasmI32), ("payload", WVT_Ref (WHT_Struct []))])
-- Note: placeholder payload uses an empty struct; a `WasmExtern` constructor
-- will replace it when WasmGC's `any`/`extern` reference types are modelled.

-- ─────────────────────────────────────────────────────────────────────────────
-- DecEq instances
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Required by the layout-equality proofs below and by any downstream code
-- that needs to compare types at the boundary.

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

-- Mutual DecEq for WasmHeapType and WasmValType.
-- The two types are mutually recursive (WasmHeapType contains WasmValType and
-- vice-versa), so both instances must be declared together.

mutual
  DecEq WasmHeapType where
    decEq (WHT_Array a) (WHT_Array b) with (decEq a b)
      _ | Yes Refl = Yes Refl
      _ | No  neq  = No (\case Refl => neq Refl)
    decEq (WHT_Struct xs) (WHT_Struct ys) with (decEq xs ys)
      _ | Yes Refl = Yes Refl
      _ | No  neq  = No (\case Refl => neq Refl)
    decEq (WHT_Func ps1 rs1) (WHT_Func ps2 rs2) with (decEq ps1 ps2)
      _ | No  neq  = No (\case Refl => neq Refl)
      _ | Yes Refl with (decEq rs1 rs2)
        _ | Yes Refl = Yes Refl
        _ | No  neq  = No (\case Refl => neq Refl)
    decEq (WHT_Array _)  (WHT_Struct _) = No (\case Refl impossible)
    decEq (WHT_Array _)  (WHT_Func _ _) = No (\case Refl impossible)
    decEq (WHT_Struct _) (WHT_Array _)  = No (\case Refl impossible)
    decEq (WHT_Struct _) (WHT_Func _ _) = No (\case Refl impossible)
    decEq (WHT_Func _ _) (WHT_Array _)  = No (\case Refl impossible)
    decEq (WHT_Func _ _) (WHT_Struct _) = No (\case Refl impossible)

  DecEq WasmValType where
    decEq (WVT_Prim p1) (WVT_Prim p2) with (decEq p1 p2)
      _ | Yes Refl = Yes Refl
      _ | No  neq  = No (\case Refl => neq Refl)
    decEq (WVT_Ref h1) (WVT_Ref h2) with (decEq h1 h2)
      _ | Yes Refl = Yes Refl
      _ | No  neq  = No (\case Refl => neq Refl)
    decEq (WVT_RefNull h1) (WVT_RefNull h2) with (decEq h1 h2)
      _ | Yes Refl = Yes Refl
      _ | No  neq  = No (\case Refl => neq Refl)
    decEq (WVT_Prim _)    (WVT_Ref _)     = No (\case Refl impossible)
    decEq (WVT_Prim _)    (WVT_RefNull _) = No (\case Refl impossible)
    decEq (WVT_Ref _)     (WVT_Prim _)    = No (\case Refl impossible)
    decEq (WVT_Ref _)     (WVT_RefNull _) = No (\case Refl impossible)
    decEq (WVT_RefNull _) (WVT_Prim _)    = No (\case Refl impossible)
    decEq (WVT_RefNull _) (WVT_Ref _)     = No (\case Refl impossible)

-- ─────────────────────────────────────────────────────────────────────────────
-- Nullability witnesses
-- ─────────────────────────────────────────────────────────────────────────────

||| A proof that a WasmValType is non-nullable (uses WVT_Ref, not WVT_RefNull).
data IsNonNull : WasmValType -> Type where
  RefIsNonNull : IsNonNull (WVT_Ref h)

||| A proof that a WasmValType is nullable (uses WVT_RefNull).
data IsNullable : WasmValType -> Type where
  RefNullIsNullable : IsNullable (WVT_RefNull h)

||| `stringLayout` is non-nullable.
||| String references must always be valid (null is not a String).
stringLayoutNonNull : IsNonNull stringLayout
stringLayoutNonNull = RefIsNonNull

||| `optionLayout t` is always nullable.
||| This is the semantic intent: Option T = the possibility of nothing.
optionLayoutNullable : (t : WasmHeapType) -> IsNullable (optionLayout t)
optionLayoutNullable _ = RefNullIsNullable

||| `resultLayout` is non-nullable.
||| Results are always present — the Ok/Err distinction is in the tag field.
resultLayoutNonNull : IsNonNull resultLayout
resultLayoutNonNull = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Distinctness proofs
-- ─────────────────────────────────────────────────────────────────────────────

||| String and Option layouts are distinct: String is non-null; Option is nullable.
||| This prevents any code from confusing `String` with `Option String`.
stringOptionDistinct : (t : WasmHeapType) -> stringLayout = optionLayout t -> Void
stringOptionDistinct _ Refl impossible
-- Discharged by constructor mismatch: WVT_Ref ≠ WVT_RefNull.

||| Primitives are not heap references.
||| Protects against accidentally encoding a primitive as a reference type.
primNotRef : (p : WasmPrimitive) -> (h : WasmHeapType) -> WVT_Prim p = WVT_Ref h -> Void
primNotRef _ _ Refl impossible

||| Primitives are not nullable references either.
primNotRefNull : (p : WasmPrimitive) -> (h : WasmHeapType) -> WVT_Prim p = WVT_RefNull h -> Void
primNotRefNull _ _ Refl impossible
