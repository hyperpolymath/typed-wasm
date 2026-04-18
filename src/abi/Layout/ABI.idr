-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- src/abi/layout/ABI.idr
--
-- Cross-language ABI conventions for WasmGC function calls.
--
-- How functions cross module boundaries between AffineScript and Ephapax:
--
--   - Primitives (i32, f64, …) are passed by value
--   - Non-nullable heap references (ref T) are passed as ByRef
--   - Nullable heap references (ref null T) are passed as ByRef
--     (the callee is responsible for null checking)
--   - Effect handlers (affine capabilities) are passed as ByAffineRef;
--     ownership transfers at the call site
--   - No raw pointer arithmetic at the ABI boundary
--
-- Proofs in this module:
--   * passConvention — the canonical mapping from WasmValType to PassingConvention
--   * primByValue    — all WVT_Prim types map to ByValue
--   * refByRef       — all WVT_Ref types map to ByRef
--   * refNullByRef   — all WVT_RefNull types map to ByRef
--   * noAffineRefForPure — ByAffineRef never appears for primitive or non-affine types
--
-- %default total enforced. No partial proofs, no totality bypasses, no coercions.

module Layout.ABI

import Layout.Types

%default total

-- ─────────────────────────────────────────────────────────────────────────────
-- Calling conventions
-- ─────────────────────────────────────────────────────────────────────────────

||| How a source-language type is passed across a WasmGC module boundary.
||| This is the agreed mapping — both consumer languages must conform.
data PassingConvention
  = ByValue WasmValType       -- primitive or small value type; copied
  | ByRef WasmHeapType        -- heap-allocated: passed as typed WasmGC reference
  | ByAffineRef WasmHeapType
    -- ^ Affine capability: ownership transferred; caller cannot use after call.
    --   Required for effect handlers (linear capabilities must not be duplicated).

||| A cross-language function signature at the ABI level.
record CrossLangSig where
  constructor MkCrossLangSig
  params  : List PassingConvention
  returns : List PassingConvention
  -- Note: WasmGC supports multi-value returns natively.

-- ─────────────────────────────────────────────────────────────────────────────
-- Canonical passing-convention function
-- ─────────────────────────────────────────────────────────────────────────────

||| The canonical mapping from a WasmGC value type to its passing convention.
|||
||| Rules:
|||   WVT_Prim p    → ByValue (WVT_Prim p)   — primitives are always copied
|||   WVT_Ref h     → ByRef h                — non-nullable heap ref
|||   WVT_RefNull h → ByRef h                — nullable heap ref (null is a valid ByRef value)
|||
||| `ByAffineRef` is NOT in scope of this function — it is applied by the
||| *affine type system* when the source language declares the parameter as
||| affine (e.g. a consumed effect handler).  That annotation lives in the
||| TypeLL L10 layer, not here.
passConvention : WasmValType -> PassingConvention
passConvention (WVT_Prim p)     = ByValue (WVT_Prim p)
passConvention (WVT_Ref h)      = ByRef h
passConvention (WVT_RefNull h)  = ByRef h

-- ─────────────────────────────────────────────────────────────────────────────
-- Proofs of the passing-convention mapping
-- ─────────────────────────────────────────────────────────────────────────────

||| Primitives are always passed by value.
primByValue : (p : WasmPrimitive) -> passConvention (WVT_Prim p) = ByValue (WVT_Prim p)
primByValue _ = Refl

||| Non-nullable heap references are always passed by reference.
refByRef : (h : WasmHeapType) -> passConvention (WVT_Ref h) = ByRef h
refByRef _ = Refl

||| Nullable heap references are passed by reference (null is a valid typed reference).
refNullByRef : (h : WasmHeapType) -> passConvention (WVT_RefNull h) = ByRef h
refNullByRef _ = Refl

||| `passConvention` never produces `ByAffineRef`.
||| Affine passing is a type-system annotation (L10), not a layout property.
noAffineRefFromPassConvention
    : (v : WasmValType)
    -> passConvention v = ByAffineRef h
    -> Void
noAffineRefFromPassConvention (WVT_Prim _)    Refl impossible
noAffineRefFromPassConvention (WVT_Ref _)     Refl impossible
noAffineRefFromPassConvention (WVT_RefNull _) Refl impossible

-- ─────────────────────────────────────────────────────────────────────────────
-- Signature helpers
-- ─────────────────────────────────────────────────────────────────────────────

||| Build a pure cross-language signature from WasmValType lists.
||| "Pure" here means no affine capabilities: all params and returns go through
||| `passConvention`, so no ByAffineRef can appear.
pureSig : List WasmValType -> List WasmValType -> CrossLangSig
pureSig ins outs = MkCrossLangSig (map passConvention ins) (map passConvention outs)

||| A pure signature never contains ByAffineRef in its parameters.
pureSigNoAffineParams
    : (ins outs : List WasmValType)
    -> All (\c => Not (c = ByAffineRef h)) (params (pureSig ins outs))
pureSigNoAffineParams [] _ = []
pureSigNoAffineParams (v :: vs) outs =
  noAffineRefFromPassConvention v :: pureSigNoAffineParams vs outs
