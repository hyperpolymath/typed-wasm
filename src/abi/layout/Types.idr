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

-- ─────────────────────────────────────────────────────────────────────────────
-- Fundamental WasmGC layout contracts
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Each type below specifies what the agreed WasmGC encoding is.  Proofs of
-- layout correctness will be added incrementally alongside the ABI
-- conventions defined in Layout.ABI and Layout.Stdlib.
--
-- Status: STUB — proofs pending.  Current file establishes the module
-- structure and naming conventions only.

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
-- TODO: replace placeholder payload struct with (ref any) when extern/any is modelled.
