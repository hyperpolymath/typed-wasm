-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- TypedAccess.idr — Typed memory access operations for typed-wasm ABI
--
-- Defines the typed memory access layer: Get, Set, and Scan operations
-- that are type-indexed by the region schema. The return type of a Get
-- is determined by the field declaration in the schema — not by the
-- programmer's choice of load instruction.
--
-- This is the "query layer" of typed-wasm: region.get is SELECT,
-- region.set is UPDATE, region.scan is SELECT * FROM ... WHERE.
--
-- Every operation requires:
-- 1. A region with a known schema (Level 2: region-binding)
-- 2. A proof that the accessed field exists (Level 2)
-- 3. Type agreement between access and declaration (Level 3)
-- 4. Bounds proof for array region access (Level 5)
--
-- The result type is computed from the schema — the caller never
-- specifies what type they expect; it flows from the field declaration.

module TypedWasm.ABI.TypedAccess

import TypedWasm.ABI.Region

%default total

-- ============================================================================
-- Idris Host Types for WASM Primitives
-- ============================================================================

||| Map a WASM primitive type to its Idris2 host representation.
||| This type family connects the WASM-level type to the Idris2 value
||| type used during proof construction and compile-time evaluation.
|||
||| At the FFI boundary (Zig layer), these map to C-ABI-compatible types.
||| At the Idris2 level, they provide the types for proof obligations.
public export
HostType : WasmType -> Type
HostType U8    = Bits8
HostType U16   = Bits16
HostType U32   = Bits32
HostType U64   = Bits64
HostType I8    = Int8
HostType I16   = Int16
HostType I32   = Int32
HostType I64   = Int64
HostType F32   = Double   -- Idris2 lacks Float32; use Double as placeholder
HostType F64   = Double
HostType WBool = Bool

-- ============================================================================
-- Access Results (Level 6: Result-Type Safety)
-- ============================================================================

||| The result of a typed memory access. The value type is determined
||| entirely by the field's WasmType — this is Level 6 (result-type safety).
|||
||| The caller of region.get does not choose the result type; it is
||| computed from the schema. If the field is declared as `i32`, the
||| result is `HostType I32 = Int32`. Period.
public export
data AccessResult : WasmType -> Type where
  ||| A successfully loaded value, carrying both the value and its type.
  MkAccessResult : (val : HostType ty) -> AccessResult ty

||| Extract the value from an access result.
public export
resultValue : AccessResult ty -> HostType ty
resultValue (MkAccessResult v) = v

-- ============================================================================
-- Get Operation (Level 2 + 3 + 5 + 6)
-- ============================================================================

||| A typed Get operation on a region. This is the typed-wasm equivalent
||| of `region.get $target .field`.
|||
||| The operation is parameterised by:
||| - `schema`: the region's schema (type-level)
||| - `name`: the field name being accessed (type-level string)
||| - `membership`: proof that `name` exists in `schema` (Level 2)
|||
||| The result type is `AccessResult (fieldType (lookupField membership))`,
||| which is fully determined by the schema — Level 3 and Level 6 combined.
public export
data Get : (schema : Schema) -> (name : String) -> Type where
  ||| Construct a Get operation for a singleton region access.
  ||| Requires a proof that the field exists in the schema.
  MkGet : (region : Region schema)
        -> (membership : FieldIn name schema)
        -> Get schema name

  ||| Construct a Get operation for an array region access at a given index.
  ||| Requires both field membership and an index bounds proof (Level 5).
  MkGetIndexed : (region : Region schema)
               -> (idx : Nat)
               -> (bounds : InBounds idx (count region))
               -> (membership : FieldIn name schema)
               -> Get schema name

||| Compute the WasmType of the field targeted by a Get operation.
||| This type is fully determined by the schema and field name — the
||| caller has no influence over it. This is Level 3 + Level 6.
public export
getResultType : {schema : _} -> Get schema name -> {auto membership : FieldIn name schema} -> WasmType
getResultType _ {membership} = fieldType (lookupField membership)

-- ============================================================================
-- Set Operation (Level 2 + 3 + 5)
-- ============================================================================

||| A typed Set operation on a region. This is the typed-wasm equivalent
||| of `region.set $target .field, value`.
|||
||| The value to write must match the field's declared type — this is
||| Level 3 (type-compatible access). The type of `val` is computed from
||| the schema, not supplied by the programmer.
public export
data Set : (schema : Schema) -> (name : String) -> Type where
  ||| Construct a Set operation for a singleton region.
  ||| The value type is forced to match the field's declared type.
  MkSet : (region : Region schema)
        -> (membership : FieldIn name schema)
        -> (val : HostType (fieldType (lookupField membership)))
        -> Set schema name

  ||| Construct a Set operation for an array region at a given index.
  ||| Requires both field membership and bounds proof.
  MkSetIndexed : (region : Region schema)
               -> (idx : Nat)
               -> (bounds : InBounds idx (count region))
               -> (membership : FieldIn name schema)
               -> (val : HostType (fieldType (lookupField membership)))
               -> Set schema name

-- ============================================================================
-- Scan Operation (Iteration over Array Regions)
-- ============================================================================

||| A predicate over a region instance, used to filter during scans.
||| The predicate receives the index and must produce a boolean.
|||
||| Analogous to a WHERE clause in SELECT * FROM region WHERE predicate.
public export
RegionPredicate : Schema -> Type
RegionPredicate schema = (idx : Nat) -> Bool

||| A Scan operation iterates over all instances of an array region,
||| optionally applying a filter predicate. This is the typed-wasm
||| equivalent of `region.scan $target where predicate`.
|||
||| The scan does not produce raw values — it produces a list of valid
||| indices that passed the predicate. Each index carries an InBounds
||| proof, so subsequent Get operations on those indices are guaranteed
||| to be within bounds (Level 5).
public export
data Scan : (schema : Schema) -> Type where
  ||| Scan all instances (no filter).
  MkScanAll : (region : Region schema)
            -> Scan schema

  ||| Scan with a filter predicate (analogous to WHERE).
  MkScanWhere : (region : Region schema)
              -> (predicate : RegionPredicate schema)
              -> Scan schema

-- ============================================================================
-- Scan Result
-- ============================================================================

||| A single scan result entry: an index paired with its bounds proof.
||| This allows subsequent access to the entry without re-proving bounds.
public export
record ScanEntry (region : Region schema) where
  constructor MkScanEntry
  ||| The index of the matching instance.
  idx : Nat
  ||| Proof that this index is within the region's bounds.
  bounds : InBounds idx (count region)

||| The result of a scan: a list of valid, bounds-proven indices.
public export
ScanResult : Region schema -> Type
ScanResult region = List (ScanEntry region)

-- ============================================================================
-- Access Type Safety Proof (Level 3)
-- ============================================================================

||| Proof that a Get operation's result type matches the field's declared
||| type. This is always true by construction (the result type IS the
||| field type), but this explicit proof serves as documentation and can
||| be composed with other proofs in the proof certificate.
|||
||| TypeSafe witnessses: "the type of the value I got from region.get
||| is exactly the type declared in the schema for that field."
public export
data TypeSafe : (name : String) -> (schema : Schema) -> (membership : FieldIn name schema) -> Type where
  ||| The access is type-safe because the result type is computed from
  ||| the field declaration. This is true by construction — there is no
  ||| other type the result could have.
  MkTypeSafe : TypeSafe name schema membership

||| Every well-formed Get is type-safe (trivially, by construction).
public export
getIsTypeSafe : (membership : FieldIn name schema) -> TypeSafe name schema membership
getIsTypeSafe _ = MkTypeSafe

-- ============================================================================
-- Byte Offset Computation for Access
-- ============================================================================

||| Compute the byte offset of a field within a region instance.
||| This is a pure function from the schema and field membership proof
||| to a natural number — no runtime calculation needed.
public export
fieldOffset : (schema : Schema) -> FieldIn name schema -> Nat
fieldOffset (f :: _) (FieldHere) = 0
fieldOffset (f :: rest) (FieldThere later) =
  let offsets = computeOffsets (f :: rest)
  in case offsets of
       [] => 0  -- impossible for non-empty schema, but keeps totality
       ((_, _) :: _) =>
         let tailOffsets = computeOffsets rest
         in case tailOffsets of
              [] => 0
              _ => fieldSize f + fieldOffset rest later

||| Compute the absolute byte address for a field access.
||| base + (index * instanceSize) + fieldOffset
public export
accessAddr : {schema : _} -> Region schema -> (idx : Nat) -> FieldIn name schema -> Nat
accessAddr {schema} r idx membership =
  baseAddr r + (idx * schemaSize schema) + fieldOffset schema membership
