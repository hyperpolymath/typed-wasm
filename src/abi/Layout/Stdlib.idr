-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- src/abi/layout/Stdlib.idr
--
-- Agreed WasmGC layouts for standard library types shared between all
-- consumer languages (AffineScript, Ephapax, and any future WasmGC target).
--
-- Every agreed layout in this module comes with:
--   1. The concrete WasmValType / WasmHeapType definition
--   2. A nullability witness (IsNonNull or IsNullable from Layout.Types)
--   3. A tag-field proof where relevant (tagged-union types)
--
-- Adding a new shared type requires:
--   a. Define the layout
--   b. Add a nullability witness
--   c. Add distinctness proofs against existing layouts (no accidental aliasing)
--   d. Open a PR on nextgen-languages/affinescript and nextgen-languages/ephapax
--      to confirm both compilers adopt the new layout
--
-- %default total enforced. No partial proofs, no totality bypasses, no coercions.

module Layout.Stdlib

import Layout.Types

%default total

-- ─────────────────────────────────────────────────────────────────────────────
-- List T
-- ─────────────────────────────────────────────────────────────────────────────
--
-- WasmGC type (isorecursive, de Bruijn):
--   μX. (struct (field "head" (ref elem)) (field "tail" (ref null X)))
-- Written with the WHT_Var/WHT_Rec constructors from Layout.Types:
--   WHT_Rec (WHT_Struct [("head", WVT_Ref elem), ("tail", WVT_RefNull (WHT_Var 0))])
--
-- WHT_Var 0 refers to the immediately enclosing WHT_Rec binder — the list node
-- struct itself.  This is the correct WasmGC encoding; no placeholder required.
--
-- Layout:
--   field "head" : (ref elem)       — the element (non-nullable; null is not an elem)
--   field "tail" : (ref null self)  — the rest; null = end of list

||| The head field: holds one element of the list.
public export
listHeadField : WasmHeapType -> (String, WasmValType)
listHeadField elem = ("head", WVT_Ref elem)

||| The tail field: a nullable self-reference.
||| WHT_Var 0 is the de Bruijn index for the enclosing WHT_Rec binder.
||| Under `WHT_Rec body`, every `WHT_Var 0` in `body` refers to the list node itself.
public export
listTailField : (String, WasmValType)
listTailField = ("tail", WVT_RefNull (WHT_Var 0))

||| The agreed WasmGC heap type for `List elem`.
||| This is the μ-binder: the self-reference in `listTailField` resolves to this node.
public export
listHeapType : WasmHeapType -> WasmHeapType
listHeapType elem = WHT_Rec (WHT_Struct [listHeadField elem, listTailField])

||| The agreed WasmGC value type for `List elem` — a non-nullable struct reference.
||| Empty lists are represented as the null tail of a containing node, not as
||| a nullable `List` reference.  This matches Ephapax's linear list design.
public export
listLayout : WasmHeapType -> WasmValType
listLayout elem = WVT_Ref (listHeapType elem)

||| List values are non-nullable references.
public export
listLayoutNonNull : (elem : WasmHeapType) -> IsNonNull (Layout.Stdlib.listLayout elem)
listLayoutNonNull _ = RefIsNonNull

||| The tail field's self-reference is exactly WHT_Var 0.
||| Proof that `listTailField` encodes the correct recursive back-reference.
public export
listTailIsVar0 : Layout.Stdlib.listTailField = ("tail", WVT_RefNull (WHT_Var 0))
listTailIsVar0 = Refl

||| The list heap type is wrapped in exactly one WHT_Rec binder.
||| This witnesses that `listHeapType` is a proper isorecursive type, not a plain struct.
public export
listHeapTypeIsRec : (elem : WasmHeapType)
    -> Layout.Stdlib.listHeapType elem
     = WHT_Rec (WHT_Struct [Layout.Stdlib.listHeadField elem, Layout.Stdlib.listTailField])
listHeapTypeIsRec _ = Refl

-- ─────────────────────────────────────────────────────────────────────────────
-- Tuple (pairs and n-tuples)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Encoding: (ref (struct (field T1) (field T2) …))
-- All fields are non-nullable; tuples are always fully initialised.

||| The agreed WasmGC heap type for a pair (T1, T2).
public export
pairHeapType : WasmValType -> WasmValType -> WasmHeapType
pairHeapType t1 t2 = WHT_Struct [("fst", t1), ("snd", t2)]

||| The agreed WasmGC value type for a pair.
public export
pairLayout : WasmValType -> WasmValType -> WasmValType
pairLayout t1 t2 = WVT_Ref (pairHeapType t1 t2)

||| Pair values are non-nullable.
public export
pairLayoutNonNull : (t1, t2 : WasmValType) -> IsNonNull (Layout.Stdlib.pairLayout t1 t2)
pairLayoutNonNull _ _ = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Function references
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Encoding: (ref (func (param T1 … Tn) (result R1 … Rm)))
-- WasmGC function references are typed by their signature.

||| The agreed WasmGC value type for a function with given param/result types.
public export
funcRefLayout : List WasmValType -> List WasmValType -> WasmValType
funcRefLayout params results = WVT_Ref (WHT_Func params results)

||| Function references are non-nullable.
public export
funcRefLayoutNonNull
    : (ps, rs : List WasmValType)
    -> IsNonNull (Layout.Stdlib.funcRefLayout ps rs)
funcRefLayoutNonNull _ _ = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Distinctness: stdlib types are pairwise distinct from core layouts
-- ─────────────────────────────────────────────────────────────────────────────

||| List layouts are distinct from String layout (different element types and structure).
public export
listNotString : (elem : WasmHeapType)
             -> Layout.Stdlib.listLayout elem = Layout.Types.stringLayout
             -> Void
listNotString _ prf = case prf of Refl impossible

||| Pair layouts are distinct from String layout.
public export
pairNotString : (t1, t2 : WasmValType)
             -> Layout.Stdlib.pairLayout t1 t2 = Layout.Types.stringLayout
             -> Void
pairNotString _ _ prf = case prf of Refl impossible

||| Function-reference layouts are distinct from String layout.
public export
funcRefNotString : (ps, rs : List WasmValType)
                -> Layout.Stdlib.funcRefLayout ps rs = Layout.Types.stringLayout
                -> Void
funcRefNotString _ _ prf = case prf of Refl impossible
