-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- src/abi/layout/ABI.idr
--
-- Cross-language ABI conventions for WasmGC function calls.
--
-- How functions cross module boundaries between AffineScript and Ephapax:
--
--   - Primitives (i32, f64) are passed by value
--   - Heap-allocated types are passed as (ref T) — typed WasmGC references
--   - Effect handlers are passed as affine capability references (transferred)
--   - No raw pointer arithmetic at the ABI boundary
--
-- Status: STUB — conventions documented; formal proofs pending.

module Layout.ABI

import Layout.Types

-- ─────────────────────────────────────────────────────────────────────────────
-- Calling conventions
-- ─────────────────────────────────────────────────────────────────────────────

||| How a source-language type is passed across a WasmGC module boundary.
||| This is the agreed mapping — both consumer languages must conform.
data PassingConvention
  = ByValue WasmValType    -- primitive or small value type
  | ByRef WasmHeapType     -- heap-allocated: passed as typed reference
  | ByAffineRef WasmHeapType
    -- ^ Affine capability: ownership transferred; caller cannot use after call

||| A cross-language function signature at the ABI level.
record CrossLangSig where
  constructor MkCrossLangSig
  params  : List PassingConvention
  returns : List PassingConvention
  -- Note: WasmGC supports multi-value returns.

-- ─────────────────────────────────────────────────────────────────────────────
-- Invariants (to be proved)
-- ─────────────────────────────────────────────────────────────────────────────

-- TODO: prove that ByValue and ByRef are the only two cases that arise for
-- pure AffineScript exports (no affine capabilities cross the boundary in
-- pure-functional exports).

-- TODO: prove that ByAffineRef is required for effect handlers (they are
-- capabilities that must not be duplicated).
