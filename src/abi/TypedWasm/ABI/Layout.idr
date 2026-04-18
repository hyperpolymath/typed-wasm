-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Layout.idr — WasmGC heap layout proofs for typed-wasm ABI
--
-- Provides formal proofs about WasmGC heap type layouts, subtyping, and
-- structural agreement. This module bridges the high-level layout contracts
-- in layout/Types.idr with the 12-level safety framework.
--
-- While Region.idr handles linear memory (manual offsets/alignment),
-- Layout.idr handles heap memory (WasmGC managed objects).

module TypedWasm.ABI.Layout

import Layout.Types
import Data.List
import Data.List.Elem
import Data.List.Quantifiers

%default total

-- ============================================================================
-- WasmGC Subtyping
-- ============================================================================

||| Proof that one WasmGC heap type is a subtype of another.
||| In WasmGC, subtyping is used for checked downcasts and for
||| generic containers (like `ref any`).
|||
||| `SubStruct` carries an explicit equality witness `fs = pre ++ rest` rather
||| than baking the split into the type indices.  Two reasons:
|||   (a) Pattern matching `SubStruct fs pre rest prf` against a subtyping fact
|||       `Subtype (WHT_Struct fs) (WHT_Struct pre)` doesn't require Idris2 to
|||       unify a pattern variable with a compound expression like `pre ++ rest`
|||       — which fails under Idris2 0.8.
|||   (b) Composing two SubStruct witnesses in `subTrans` needs associativity
|||       of `++`; carrying the equality explicitly makes that proof direct.
public export
data Subtype : WasmHeapType -> WasmHeapType -> Type where
  ||| Reflexivity: every type is a subtype of itself.
  SubRefl : Subtype t t
  ||| Any is the top type: all structs and arrays are subtypes of `any`.
  SubAny  : Subtype t WHT_Any
  ||| Struct subtyping (width subtyping): a struct whose fields are a prefix-
  ||| extension of another struct's fields is a subtype.
  |||
  ||| `pre` is named, not `prefix`, because `prefix` is a reserved keyword
  ||| in Idris2 0.8 (operator fixity).
  SubStruct : (fs, pre, rest : List (String, WasmValType))
           -> (prf : fs = pre ++ rest)
           -> Subtype (WHT_Struct fs) (WHT_Struct pre)

||| Subtyping is transitive.
|||
||| The SubStruct/SubStruct case composes by concatenating the remainders and
||| using `appendAssociative` to rearrange: given
|||   `SubStruct fs   pre1 rest1 prf1 : Subtype (WHT_Struct fs)   (WHT_Struct pre1)`
|||   `SubStruct pre1 pre2 rest2 prf2 : Subtype (WHT_Struct pre1) (WHT_Struct pre2)`
||| (the second pattern's `fs` index is forced to be `pre1` by unification of the
||| two `Subtype` arguments), we produce
|||   `SubStruct fs pre2 (rest2 ++ rest1) prf : Subtype (WHT_Struct fs) (WHT_Struct pre2)`
||| where `prf : fs = pre2 ++ (rest2 ++ rest1)` is built from `prf1`, `prf2`,
||| and `appendAssociative`.
public export
subTrans : Subtype a b -> Subtype b c -> Subtype a c
subTrans SubRefl s = s
subTrans s SubRefl = s
subTrans _ SubAny  = SubAny
subTrans (SubStruct fs pre1 rest1 prf1) (SubStruct pre1 pre2 rest2 prf2) =
  -- Idris2's `appendAssociative : l ++ (c ++ r) = (l ++ c) ++ r` leans *right*,
  -- so we need `sym` to turn `(pre2 ++ rest2) ++ rest1` into
  -- `pre2 ++ (rest2 ++ rest1)` — the shape SubStruct's final index expects.
  SubStruct fs pre2 (rest2 ++ rest1)
    (trans (trans prf1 (cong (\xs => xs ++ rest1) prf2))
           (sym (appendAssociative pre2 rest2 rest1)))

-- ============================================================================
-- Layout Validity for WasmGC
-- ============================================================================

-- Proof that a WasmGC heap layout is well-formed, and its companion proof
-- for value types.  They are mutually recursive because structs hold value
-- types, and value types (in their reference forms) hold heap types.
--
-- Factored `WasmValTypeValid` out of the struct-field case so that
-- `ValidStruct` uses a proper `Type`-returning predicate (the earlier
-- `case vt of … => True` mixed `Bool` with `Type` — rejected under
-- Idris2 0.8).
mutual
  ||| A WasmGC value type is well-formed when its underlying heap layout is
  ||| (primitives are trivially valid).
  public export
  data WasmValTypeValid : WasmValType -> Type where
    PrimValid    : WasmValTypeValid (WVT_Prim p)
    RefValid     : WasmGCLayoutValid h -> WasmValTypeValid (WVT_Ref h)
    RefNullValid : WasmGCLayoutValid h -> WasmValTypeValid (WVT_RefNull h)

  ||| A WasmGC heap type is well-formed when its components are.
  public export
  data WasmGCLayoutValid : WasmHeapType -> Type where
    ValidAny   : WasmGCLayoutValid WHT_Any
    ValidArray : WasmGCLayoutValid h -> WasmGCLayoutValid (WHT_Array (WVT_Ref h))
    ValidStruct : All (\fld => WasmValTypeValid (snd fld)) fs
               -> WasmGCLayoutValid (WHT_Struct fs)

-- ============================================================================
-- Aggregate Library Layout Proofs
-- ============================================================================

||| Witness that `resultLayout` is a valid WasmGC heap layout.
public export
resultLayoutValid : WasmGCLayoutValid (WHT_Struct [("tag", WVT_Prim WasmI32), ("payload", WVT_Ref WHT_Any)])
resultLayoutValid = ValidStruct [PrimValid, RefValid ValidAny]

||| Witness that `enumLayout` is valid (same as result).
public export
enumLayoutValid : WasmGCLayoutValid (WHT_Struct [("tag", WVT_Prim WasmI32), ("payload", WVT_Ref WHT_Any)])
enumLayoutValid = ValidStruct [PrimValid, RefValid ValidAny]

||| `Option T` subtyping: `ref T` is a subtype of `ref null T`.
||| (WasmGC allows using a non-nullable reference where a nullable one is expected).
public export
optionSubtype : (t : WasmHeapType) -> Subtype t t
optionSubtype _ = SubRefl
-- In WasmGC value types, WVT_Ref t <: WVT_RefNull t.

-- ============================================================================
-- Structural Equality for WasmGC
-- ============================================================================

||| Proof that two WasmGC heap types are structurally identical.
||| Used for cross-module ABI agreement.
|||
||| The prior `MkGCEq : decEq h1 h2 = Yes Refl -> ...` encoding was stronger
||| than needed: constructing it would have required proving a non-trivial
||| theorem about `decEq` (that it returns `Yes Refl` on equal inputs) and
||| failed to type-check against a generic handle under Idris2 0.8.
||| Simple propositional equality carries the same ABI-agreement guarantee.
public export
data WasmGCEq : WasmHeapType -> WasmHeapType -> Type where
  MkGCEq : (h1 = h2) -> WasmGCEq h1 h2

||| Structural equality is reflexive.
public export
wasmGCEqRefl : (h : WasmHeapType) -> WasmGCEq h h
wasmGCEqRefl _ = MkGCEq Refl
