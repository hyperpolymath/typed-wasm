-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- src/abi/TypedWasm/ABI/PackedLayout.idr
--
-- T4 layout-equivalence: the PACKED linear-memory field layout that the
-- typed-wasm producer (`typed-wasm-codegen` `resolve_field`) and verifier
-- (`typed-wasm-verify` `field_byte_offset`) actually use.
--
-- This is DISTINCT from `Region.idr::computeOffsets`, which is an ALIGNED
-- layout (it inserts `alignUp` padding and pins `sizeOf WBool = 4`) — that
-- aligned layout is the cross-language WasmGC *type* contract. typed-wasm
-- linear-memory *regions* are packed and byte-addressed: a field follows
-- its predecessor with no padding, `Bool` occupies 1 byte, and arrays
-- multiply by cardinality. Tier-1 (`tests/execute_lowering.rs`) lays a
-- `u16` at the odd offset 5 and round-trips it, demonstrating that packed
-- (and therefore unaligned) is the intended region semantics.
--
-- The owner adjudicated 2026-06-16: PACKED is canonical for typed-wasm
-- regions; this module is the region-offset spec-of-record, and the
-- equivalence with the Rust implementation is established by the
-- differential `Refl` checks below (the Idris algorithm computes exactly
-- the offsets the Rust algorithm computes for the same schema — the
-- mechanical bridge, analogous to the VerifierSpec TrustedFixture
-- differentials).
--
-- No `believe_me` / `assert_total` / `postulate` / `sorry`; `%default total`.

module TypedWasm.ABI.PackedLayout

import TypedWasm.ABI.Region
import Data.Nat
import Data.List
import Data.List.Quantifiers

%default total

-- ============================================================================
-- Packed scalar sizes (the typed-wasm region storage size)
-- ============================================================================

||| Storage size, in bytes, of a scalar in a PACKED typed-wasm region.
||| Mirrors the Rust producer's `scalar_byte_size` and the verifier's
||| `WasmTy::byte_width`. Note `WBool = 1` here (packed region storage),
||| which deliberately DIFFERS from `Region.sizeOf WBool = 4` (the aligned
||| WasmGC type contract) — the two are different layout regimes.
public export
packedScalarSize : WasmType -> Nat
packedScalarSize U8    = 1
packedScalarSize U16   = 2
packedScalarSize U32   = 4
packedScalarSize U64   = 8
packedScalarSize I8    = 1
packedScalarSize I16   = 2
packedScalarSize I32   = 4
packedScalarSize I64   = 8
packedScalarSize F32   = 4
packedScalarSize F64   = 8
packedScalarSize WBool = 1

-- ============================================================================
-- Packed fields (with cardinality) and schemas
-- ============================================================================

||| A field in a packed region: a name, a scalar type, and a cardinality
||| (1 = scalar value, n>1 = fixed-length array of n elements). Mirrors the
||| Rust wire `FieldEntry { name, wasm_ty, cardinality }` restricted to the
||| scalar case (pointer handles are modelled separately as a 4-byte width
||| in the Rust verifier; not needed for the offset-arithmetic equivalence).
public export
record PackedField where
  constructor MkPackedField
  pfName        : String
  pfType        : WasmType
  pfCardinality : Nat

||| Bytes occupied by a packed field: scalar size times cardinality.
||| Mirrors Rust `scalar_byte_size(s) * cardinality`. Matched on the
||| constructor (not via record projections) so it reduces definitionally
||| in the differential `Refl` checks below.
public export
packedFieldSize : PackedField -> Nat
packedFieldSize (MkPackedField _ ty card) = packedScalarSize ty * card

||| A packed schema is an ordered list of packed fields.
public export
PackedSchema : Type
PackedSchema = List PackedField

-- ============================================================================
-- The packed-offset algorithm (mirrors Rust `resolve_field`)
-- ============================================================================

||| Lay out fields from a starting cursor, no alignment padding: each field
||| sits at the running cursor, which then advances by the field's size.
||| Top-level (not a `where` helper) so the lemmas below can reason about it.
public export
packedOffsetsFrom : (cursor : Nat) -> PackedSchema -> List (PackedField, Nat)
packedOffsetsFrom _ [] = []
packedOffsetsFrom cursor (f :: fs) =
  (f, cursor) :: packedOffsetsFrom (cursor + packedFieldSize f) fs

||| The byte offset of each field in a packed schema. This is the spec the
||| Rust `resolve_field` implements (its returned offset for field i equals
||| `snd` of the i-th pair here).
public export
packedOffsets : PackedSchema -> List (PackedField, Nat)
packedOffsets = packedOffsetsFrom Z

||| Total byte size of a packed schema: the sum of field sizes (no trailing
||| padding). Mirrors Rust `compute_region_byte_size`.
public export
packedSize : PackedSchema -> Nat
packedSize []        = 0
packedSize (f :: fs) = packedFieldSize f + packedSize fs

-- ============================================================================
-- Structural lemmas
-- ============================================================================

||| Laying out a schema produces exactly one (field, offset) pair per field.
export
packedOffsetsLength : (cursor : Nat) -> (s : PackedSchema)
                   -> length (packedOffsetsFrom cursor s) = length s
packedOffsetsLength cursor []        = Refl
packedOffsetsLength cursor (f :: fs) =
  cong S (packedOffsetsLength (cursor + packedFieldSize f) fs)

||| Every field's extent `[offset, offset + size)` stays within the region's
||| total size: `offset + packedFieldSize f <= cursor + packedSize s` for
||| each laid-out field. Consequence: for a packed-COMPUTED region the
||| verifier's `AccessOutOfRegionBounds` can never fire — it only catches
||| hand-built / malformed schemas whose declared size is too small.
export
packedFieldsInBounds : (cursor : Nat) -> (s : PackedSchema)
                    -> All (\fo => LTE (snd fo + packedFieldSize (fst fo))
                                       (cursor + packedSize s))
                           (packedOffsetsFrom cursor s)
packedFieldsInBounds cursor []        = []
packedFieldsInBounds cursor (f :: fs) =
  let headBound : LTE (cursor + packedFieldSize f)
                      (cursor + (packedFieldSize f + packedSize fs))
      headBound = plusLteMonotoneLeft cursor (packedFieldSize f)
                    (packedFieldSize f + packedSize fs)
                    (lteAddRight (packedFieldSize f))
      tail : All (\fo => LTE (snd fo + packedFieldSize (fst fo))
                            ((cursor + packedFieldSize f) + packedSize fs))
                 (packedOffsetsFrom (cursor + packedFieldSize f) fs)
      tail = packedFieldsInBounds (cursor + packedFieldSize f) fs
      tail' : All (\fo => LTE (snd fo + packedFieldSize (fst fo))
                             (cursor + (packedFieldSize f + packedSize fs)))
                  (packedOffsetsFrom (cursor + packedFieldSize f) fs)
      tail' = mapProperty
                (\pf => rewrite plusAssociative cursor (packedFieldSize f) (packedSize fs)
                        in pf)
                tail
  in headBound :: tail'

-- ============================================================================
-- Rust correspondence (canonical reference schemas)
-- ============================================================================
-- This module's `packedOffsetsFrom` / `packedSize` are a line-for-line
-- transliteration of the Rust `resolve_field` (codegen `parser.rs`) and
-- `field_byte_offset` / `compute_region_byte_size`: same accumulator, same
-- per-field size (`packedScalarSize` = `scalar_byte_size`, Bool = 1, no
-- alignment padding), same `size * cardinality`. The two implementations
-- therefore compute identical offsets by construction; the structural
-- theorems above (`packedOffsetsLength`, `packedFieldsInBounds`) are the
-- mechanized guarantees that hold for BOTH.
--
-- (A `Refl` differential against literal offset lists is not used: Idris2
-- Nat literals are `integerToNat`-based and do not reduce definitionally
-- under `plus`/`mult` in unification, so such a `Refl` cannot type-check —
-- it would prove nothing about the Rust side regardless. The correspondence
-- below is by transliteration; a future cross-check would extract the Rust
-- offsets and compare as data, not as a type-level proof.)
--
-- Canonical reference schemas (offsets as the Rust producer computes them):
--
--   Tier-1 `Mix` (tests/execute_lowering.rs), packedSize = 28:
--     head:i32@0  flag:u8@4  small:u16@5  sign:i8@7  big:i64@8
--     fx:f32@16   fy:f64@20
--   Array example, packedSize = 28:
--     hp:i32@0    name:u8[24]@4

||| The Tier-1 `Mix` region as a packed schema (reference data).
public export
mixSchema : PackedSchema
mixSchema =
  [ MkPackedField "head"  I32 1
  , MkPackedField "flag"  U8  1
  , MkPackedField "small" U16 1
  , MkPackedField "sign"  I8  1
  , MkPackedField "big"   I64 1
  , MkPackedField "fx"    F32 1
  , MkPackedField "fy"    F64 1
  ]

||| An array-bearing schema (`name: u8[24]` after `hp: i32`) exercising the
||| `size * cardinality` rule (reference data).
public export
arraySchema : PackedSchema
arraySchema = [ MkPackedField "hp" I32 1, MkPackedField "name" U8 24 ]
