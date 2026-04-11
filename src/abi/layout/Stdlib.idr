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
-- No believe_me, assert_total, or unsafe patterns permitted.

module Layout.Stdlib

import Layout.Types

%default total

-- ─────────────────────────────────────────────────────────────────────────────
-- List T
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Encoding: (ref (struct (field T-or-null) (field (ref null self))))
-- i.e. a linked-list node where:
--   field 0 "head": (ref T) — the element (non-nullable)
--   field 1 "tail": (ref null List) — the rest, nullable (null = empty list)
--
-- Note: this encoding uses WasmGC recursive types.  The `self` reference
-- is represented here by an empty struct placeholder until WasmGC recursive
-- types are modelled in this Idris2 framework.

||| The element slot in a List node.
||| For a List of elements of heap type `elem`, the head field holds a (ref elem).
listHeadField : WasmHeapType -> (String, WasmValType)
listHeadField elem = ("head", WVT_Ref elem)

||| The tail slot in a List node — nullable because the empty list is null.
||| The tail heap type is a placeholder empty struct; in real WasmGC this would
||| be a recursive self-reference to the list struct type.
listTailField : (String, WasmValType)
listTailField = ("tail", WVT_RefNull (WHT_Struct []))
-- Note: replace the placeholder WHT_Struct [] with the actual recursive type
-- when WasmGC recursive references are modelled.

||| The agreed WasmGC heap type for `List elem`.
listHeapType : WasmHeapType -> WasmHeapType
listHeapType elem = WHT_Struct [listHeadField elem, listTailField]

||| The agreed WasmGC value type for `List elem` — a non-nullable struct reference.
||| Empty lists are represented as the null tail of a containing node, not as
||| a nullable `List` reference itself.  This matches Ephapax's linear list design.
listLayout : WasmHeapType -> WasmValType
listLayout elem = WVT_Ref (listHeapType elem)

||| List values are non-nullable references.
listLayoutNonNull : (elem : WasmHeapType) -> IsNonNull (listLayout elem)
listLayoutNonNull _ = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Tuple (pairs and n-tuples)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Encoding: (ref (struct (field T1) (field T2) …))
-- All fields are non-nullable; tuples are always fully initialised.

||| The agreed WasmGC heap type for a pair (T1, T2).
pairHeapType : WasmValType -> WasmValType -> WasmHeapType
pairHeapType t1 t2 = WHT_Struct [("fst", t1), ("snd", t2)]

||| The agreed WasmGC value type for a pair.
pairLayout : WasmValType -> WasmValType -> WasmValType
pairLayout t1 t2 = WVT_Ref (pairHeapType t1 t2)

||| Pair values are non-nullable.
pairLayoutNonNull : (t1 t2 : WasmValType) -> IsNonNull (pairLayout t1 t2)
pairLayoutNonNull _ _ = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Function references
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Encoding: (ref (func (param T1 … Tn) (result R1 … Rm)))
-- WasmGC function references are typed by their signature.

||| The agreed WasmGC value type for a function with given param/result types.
funcRefLayout : List WasmValType -> List WasmValType -> WasmValType
funcRefLayout params results = WVT_Ref (WHT_Func params results)

||| Function references are non-nullable.
funcRefLayoutNonNull
    : (ps rs : List WasmValType)
    -> IsNonNull (funcRefLayout ps rs)
funcRefLayoutNonNull _ _ = RefIsNonNull

-- ─────────────────────────────────────────────────────────────────────────────
-- Distinctness: stdlib types are pairwise distinct from core layouts
-- ─────────────────────────────────────────────────────────────────────────────

||| List layouts are distinct from String layout (different element types and structure).
listNotString : (elem : WasmHeapType) -> listLayout elem = stringLayout -> Void
listNotString _ Refl impossible

||| Pair layouts are distinct from String layout.
pairNotString : (t1 t2 : WasmValType) -> pairLayout t1 t2 = stringLayout -> Void
pairNotString _ _ Refl impossible

||| Function-reference layouts are distinct from String layout.
funcRefNotString : (ps rs : List WasmValType) -> funcRefLayout ps rs = stringLayout -> Void
funcRefNotString _ _ Refl impossible
