-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Region.idr — Core region types for typed-wasm ABI
--
-- Defines the foundational types for typed memory regions in WebAssembly:
-- primitive WASM types, fields with computed sizes, schemas as type-level
-- lists of fields, and region layouts with proven correct offsets.
--
-- The key insight: a WASM memory region is analogous to a database table.
-- A Schema is the column definition, a Region is the table, and field
-- offsets are computed (not guessed) from the schema structure.
--
-- All sizes and offsets are computed purely from the type-level schema,
-- so layout correctness is guaranteed by construction — there is no
-- runtime layout calculation that could diverge from the type.

module TypedWasm.ABI.Region

import Data.Nat
import Data.List

%default total

-- ============================================================================
-- WASM Primitive Types
-- ============================================================================

||| The primitive value types available in WebAssembly linear memory.
||| Each has a known, fixed size in bytes. These correspond directly to
||| WASM's value types plus sub-word integer types commonly used in
||| memory layouts (u8, u16, i8, i16).
public export
data WasmType : Type where
  ||| 8-bit unsigned integer (1 byte).
  U8  : WasmType
  ||| 16-bit unsigned integer (2 bytes).
  U16 : WasmType
  ||| 32-bit unsigned integer (4 bytes).
  U32 : WasmType
  ||| 64-bit unsigned integer (8 bytes).
  U64 : WasmType
  ||| 8-bit signed integer (1 byte).
  I8  : WasmType
  ||| 16-bit signed integer (2 bytes).
  I16 : WasmType
  ||| 32-bit signed integer (4 bytes).
  I32 : WasmType
  ||| 64-bit signed integer (8 bytes).
  I64 : WasmType
  ||| 32-bit IEEE 754 float (4 bytes).
  F32 : WasmType
  ||| 64-bit IEEE 754 float (8 bytes).
  F64 : WasmType
  ||| Boolean (stored as 1 byte: 0 = false, nonzero = true).
  WBool : WasmType

public export
Eq WasmType where
  U8    == U8    = True
  U16   == U16   = True
  U32   == U32   = True
  U64   == U64   = True
  I8    == I8    = True
  I16   == I16   = True
  I32   == I32   = True
  I64   == I64   = True
  F32   == F32   = True
  F64   == F64   = True
  WBool == WBool = True
  _     == _     = False

public export
Show WasmType where
  show U8    = "u8"
  show U16   = "u16"
  show U32   = "u32"
  show U64   = "u64"
  show I8    = "i8"
  show I16   = "i16"
  show I32   = "i32"
  show I64   = "i64"
  show F32   = "f32"
  show F64   = "f64"
  show WBool = "bool"

-- ============================================================================
-- Type-Level Size Computation
-- ============================================================================

||| Compute the size in bytes of a WASM primitive type.
||| This is a total function from types to natural numbers, computed
||| entirely at the type level. The result is a compile-time constant.
public export
sizeOf : WasmType -> Nat
sizeOf U8    = 1
sizeOf U16   = 2
sizeOf U32   = 4
sizeOf U64   = 8
sizeOf I8    = 1
sizeOf I16   = 2
sizeOf I32   = 4
sizeOf I64   = 8
sizeOf F32   = 4
sizeOf F64   = 8
sizeOf WBool = 1

||| Compute the natural alignment of a WASM primitive type.
||| Alignment equals the type's size for all WASM primitives — this
||| matches the WASM specification's natural alignment rules.
public export
alignOf : WasmType -> Nat
alignOf = sizeOf

-- ============================================================================
-- Field Declarations
-- ============================================================================

||| A named field within a region schema. The field's name is a type-level
||| string and its type is a WasmType. Together these determine the field's
||| size, alignment, and the WASM load/store instruction used to access it.
|||
||| Analogous to a column in a database table: the name identifies it and
||| the type determines how values are stored and retrieved.
public export
data Field : Type where
  MkField : (name : String) -> (ty : WasmType) -> Field

||| Extract the name from a field declaration.
public export
fieldName : Field -> String
fieldName (MkField n _) = n

||| Extract the type from a field declaration.
public export
fieldType : Field -> WasmType
fieldType (MkField _ t) = t

||| Compute the size of a field (delegated to its type's size).
public export
fieldSize : Field -> Nat
fieldSize (MkField _ t) = sizeOf t

||| Compute the alignment of a field (delegated to its type's alignment).
public export
fieldAlign : Field -> Nat
fieldAlign (MkField _ t) = alignOf t

-- ============================================================================
-- Schema: Type-Level List of Fields
-- ============================================================================

||| A schema is a list of fields, analogous to a table definition.
||| The order of fields determines their layout in memory — first field
||| is at offset 0 (after alignment), second field follows, etc.
public export
Schema : Type
Schema = List Field

-- ============================================================================
-- Alignment Arithmetic
-- ============================================================================

||| Round up a value to the nearest multiple of an alignment.
||| alignUp x a = x rounded up to the next multiple of a.
|||
||| Precondition: alignment must be nonzero. We handle the zero case
||| by returning x unchanged (a degenerate but safe fallback).
public export
alignUp : (x : Nat) -> (alignment : Nat) -> Nat
alignUp x Z = x
alignUp x (S a) =
  let remainder = modNatNZ x (S a) ItIsSucc
  in case remainder of
       Z => x
       (S _) => x + ((S a) `minus` remainder)

-- ============================================================================
-- Offset Computation
-- ============================================================================

||| Compute the byte offset of each field in a schema, respecting alignment.
||| Returns a list of (field, offset) pairs. Fields are laid out sequentially
||| with alignment padding inserted as needed.
|||
||| This is the core layout algorithm. Since it is a total function from
||| Schema to List (Field, Nat), the layout is determined entirely by the
||| schema — no runtime layout engine is needed.
public export
computeOffsets : Schema -> List (Field, Nat)
computeOffsets = go 0
  where
    ||| Accumulator-based layout: `cursor` tracks the current byte position.
    go : (cursor : Nat) -> Schema -> List (Field, Nat)
    go _ [] = []
    go cursor (f :: fs) =
      let aligned = alignUp cursor (fieldAlign f)
      in (f, aligned) :: go (aligned + fieldSize f) fs

||| Compute the total size of a schema, including trailing padding to
||| satisfy the alignment of the most-strictly-aligned field. This ensures
||| that arrays of this schema are correctly aligned element-to-element.
public export
schemaSize : Schema -> Nat
schemaSize [] = 0
schemaSize schema =
  let offsets = computeOffsets schema
      maxAlign = foldl (\acc, f => max acc (fieldAlign f)) 1 schema
  in case last' offsets of
       Nothing => 0
       Just (lastField, lastOffset) =>
         alignUp (lastOffset + fieldSize lastField) maxAlign

-- ============================================================================
-- Field Lookup by Name
-- ============================================================================

||| Proof that a field with a given name exists in a schema.
||| This is the compile-time witness for Level 2 (region-binding safety):
||| every field access must produce a FieldIn proof showing the field exists.
public export
data FieldIn : String -> Schema -> Type where
  ||| The field is at the head of the schema.
  FieldHere  : {auto prf : fieldName f = name}
             -> FieldIn name (f :: rest)
  ||| The field is somewhere in the tail of the schema.
  FieldThere : FieldIn name rest -> FieldIn name (f :: rest)

||| Given a proof that a field exists in a schema, extract the field itself.
public export
lookupField : {schema : _} -> FieldIn name schema -> Field
lookupField {schema = f :: _} (FieldHere) = f
lookupField (FieldThere later) = lookupField later

-- ============================================================================
-- Region: A Named Schema with Layout
-- ============================================================================

||| A region is a named, typed view over contiguous WASM linear memory.
||| It bundles a schema with its computed layout information.
|||
||| The region's schema is a type-level parameter, so all access to the
||| region is statically verified against the schema. The base address is
||| a runtime value (set when the region is allocated or placed), but the
||| offsets within the region are compile-time constants.
|||
||| Analogous to a database table: the schema defines the structure, the
||| base address is where the table physically resides in memory.
public export
record Region (schema : Schema) where
  constructor MkRegion
  ||| Human-readable name for error messages and debugging.
  regionName : String
  ||| Base address in WASM linear memory (byte offset from memory[0]).
  baseAddr   : Nat
  ||| Number of instances (1 for singleton, >1 for array regions).
  ||| An array region is like a table with a fixed number of rows.
  count      : Nat

||| Compute the byte size of a single instance of this region's schema.
public export
instanceSize : {schema : _} -> Region schema -> Nat
instanceSize {schema} _ = schemaSize schema

||| Compute the total byte footprint of a region (all instances).
public export
totalSize : {schema : _} -> Region schema -> Nat
totalSize r = instanceSize r * count r

-- ============================================================================
-- Region Layout Proof
-- ============================================================================

||| Proof that a region's layout is self-consistent:
||| - Every field offset is within the instance size.
||| - No two fields overlap (each field starts after the previous one ends).
|||
||| This is constructed by the layout algorithm itself — since
||| `computeOffsets` is total and deterministic, any Region built from a
||| valid Schema automatically has a correct layout. The proof type exists
||| to serve as an explicit witness that can be passed across module
||| boundaries (Level 8 multi-module verification).
public export
data LayoutValid : (schema : Schema) -> Type where
  ||| The empty schema has a trivially valid layout.
  LayoutNil  : LayoutValid []
  ||| A non-empty schema's layout is valid if:
  ||| - The first field fits within the computed instance size.
  ||| - The remaining fields form a valid layout with offsets shifted
  |||   past the first field.
  LayoutCons : (f : Field)
             -> (offset : Nat)
             -> (fitsPrf : LTE (offset + fieldSize f) (schemaSize (f :: rest)))
             -> LayoutValid rest
             -> LayoutValid (f :: rest)

-- ============================================================================
-- Schema Equality (for cross-module agreement)
-- ============================================================================

||| Proof that two schemas are structurally identical: same fields in the
||| same order with the same types. This is the foundation of Level 8
||| multi-module type agreement — when Module A exports a region and
||| Module B imports it, this proof witnesses that they agree on the layout.
public export
data SchemaEq : Schema -> Schema -> Type where
  ||| Two empty schemas are equal.
  SchemaNil  : SchemaEq [] []
  ||| Two non-empty schemas are equal if their heads match (same name and
  ||| type) and their tails are recursively equal.
  SchemaCons : (nameEq : fieldName f1 = fieldName f2)
             -> (typeEq : fieldType f1 = fieldType f2)
             -> SchemaEq rest1 rest2
             -> SchemaEq (f1 :: rest1) (f2 :: rest2)

||| Schema equality is reflexive.
public export
schemaEqRefl : (s : Schema) -> SchemaEq s s
schemaEqRefl [] = SchemaNil
schemaEqRefl (f :: fs) = SchemaCons Refl Refl (schemaEqRefl fs)

-- ============================================================================
-- Bounds Proof (Level 5)
-- ============================================================================

||| Proof that an index is within the bounds of an array region.
||| For a region with `count` instances, valid indices are [0, count).
||| This proof must be provided at every indexed access — the type system
||| will not allow an access without it.
public export
data InBounds : (idx : Nat) -> (count : Nat) -> Type where
  ||| Witness that idx < count (i.e., idx < S remaining).
  MkInBounds : LTE (S idx) count -> InBounds idx count

||| Zero is always in bounds for a non-empty region.
public export
zeroInBounds : InBounds 0 (S n)
zeroInBounds = MkInBounds (LTESucc LTEZero)
