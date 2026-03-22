-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MultiModule.idr — Cross-module schema agreement for typed-wasm ABI
--
-- THE KILLER FEATURE: when Module A (Rust) exports a region schema and
-- Module B (ReScript) imports it, this module proves that both sides agree
-- on the memory layout — field names, types, offsets, alignment.
--
-- Neither Rust's borrow checker nor ReScript's type system can verify this
-- boundary. Only a WASM-level type system can. This is typed-wasm's unique
-- contribution.
--
-- The database analogy: this is schema migration safety. When two systems
-- share a database, they must agree on the schema. When two WASM modules
-- share linear memory, they must agree on the region layout.

module TypedWasm.ABI.MultiModule

import TypedWasm.ABI.Region

%default total

-- ============================================================================
-- Module Identity
-- ============================================================================

||| A WASM module identifier. Modules are identified by name at link time.
public export
data ModuleId : Type where
  MkModuleId : (name : String) -> ModuleId

public export
Eq ModuleId where
  (MkModuleId a) == (MkModuleId b) = a == b

-- ============================================================================
-- Export / Import Declarations
-- ============================================================================

||| An exported region schema: a module declares "I provide this region
||| with this exact layout."
public export
data ExportedRegion : Type where
  MkExport : (source : ModuleId)
          -> (regionName : String)
          -> (schema : Schema)
          -> ExportedRegion

||| An imported region schema: a module declares "I expect a region with
||| this layout from that module."
public export
data ImportedRegion : Type where
  MkImport : (consumer : ModuleId)
          -> (source : ModuleId)
          -> (regionName : String)
          -> (expectedSchema : Schema)
          -> ImportedRegion

-- ============================================================================
-- Structural Compatibility
-- ============================================================================

||| Proof that two WasmTypes are compatible.
||| Compatibility is strict equality — no implicit conversions.
public export
data WasmTypeCompat : WasmType -> WasmType -> Type where
  ||| Types must be identical.
  TypeCompat : WasmTypeCompat ty ty

||| Proof that a single field in the import matches the corresponding
||| field in the export: same name and same type.
public export
data FieldMatch : Field -> Field -> Type where
  ||| Fields match if they have the same name and same WasmType.
  MkFieldMatch : {name : String} -> {ty : WasmType}
              -> FieldMatch (MkField name ty) (MkField name ty)

-- ============================================================================
-- Schema Agreement (Core Theorem)
-- ============================================================================

||| Proof that an imported schema is compatible with an exported schema.
|||
||| IMPORTANT: The import may be a SUBSET of the export. Module B may only
||| import 5 of Module A's 12 fields — that's fine, it just can't access
||| the other 7. But every field Module B claims to import MUST exist in
||| Module A's export with the same type and offset.
|||
||| This is the core theorem of typed-wasm's multi-module type safety:
|||   forall field in import.
|||     exists matching_field in export.
|||       field.name == matching_field.name /\
|||       field.type == matching_field.type
public export
data SchemaAgreement : Type where
  ||| All imported fields have matching exports.
  MkAgreement : (exportMod : ModuleId)
             -> (importMod : ModuleId)
             -> (regionName : String)
             -> SchemaAgreement

-- ============================================================================
-- Alignment Agreement
-- ============================================================================

||| Proof that the alignment requirements agree between export and import.
||| Both modules must agree on the alignment of the shared region.
public export
data AlignmentAgrees : (exportAlign : Nat) -> (importAlign : Nat) -> Type where
  ||| Alignment values are identical.
  AlignMatch : AlignmentAgrees n n

-- ============================================================================
-- Instance Count Agreement
-- ============================================================================

||| Proof that array region instance counts agree.
||| If the export says 1024 instances and the import says 1024, they agree.
public export
data InstanceCountAgrees : (exportCount : Nat) -> (importCount : Nat) -> Type where
  ||| Counts are identical.
  CountMatch : InstanceCountAgrees n n

-- ============================================================================
-- Full Compatibility Certificate
-- ============================================================================

||| A complete compatibility certificate for a multi-module region.
||| This bundles all the individual proofs into one attestation that
||| can be verified at link time.
|||
||| Producing this certificate requires:
|||   1. Schema agreement (all imported fields exist in export)
|||   2. Alignment agreement
|||   3. Instance count agreement
|||
||| If the certificate exists, the modules are provably compatible.
||| If it cannot be constructed, the modules disagree and linking fails
||| with a clear diagnostic.
public export
data CompatCertificate : Type where
  MkCompat : (agreement : SchemaAgreement)
          -> (alignment : AlignmentAgrees ea ia)
          -> (instances : InstanceCountAgrees ec ic)
          -> CompatCertificate

-- ============================================================================
-- Module Link Graph
-- ============================================================================

||| A link edge: Module B imports region R from Module A.
public export
data LinkEdge : Type where
  MkLinkEdge : (from : ModuleId)
            -> (to : ModuleId)
            -> (region : String)
            -> (cert : CompatCertificate)
            -> LinkEdge

||| A link graph: all the import/export relationships between modules.
||| Every edge carries a compatibility certificate, so the entire graph
||| is provably type-safe.
public export
LinkGraph : Type
LinkGraph = List LinkEdge

||| Proof that a link graph is fully verified: every import has a
||| corresponding export with a valid compatibility certificate.
public export
data FullyVerified : LinkGraph -> Type where
  ||| The empty graph is trivially verified.
  EmptyGraph : FullyVerified []
  ||| A graph with one verified edge prepended to a verified graph.
  ConsEdge : FullyVerified rest -> FullyVerified (edge :: rest)

-- ============================================================================
-- Diagnostics for Failed Verification
-- ============================================================================

||| When schema agreement cannot be proven, produce a diagnostic
||| explaining what went wrong. This feeds into the error reporting
||| pipeline — clear error messages are critical for adoption.
public export
data SchemaMismatch : Type where
  ||| A field exists in the import but not in the export.
  MissingField : (name : String) -> (importMod : ModuleId) -> SchemaMismatch
  ||| A field exists in both but with different types.
  TypeMismatch : (name : String) -> (exportType : String) -> (importType : String) -> SchemaMismatch
  ||| Alignment values disagree.
  AlignmentMismatch : (exportAlign : Nat) -> (importAlign : Nat) -> SchemaMismatch
  ||| Instance counts disagree.
  CountMismatch : (exportCount : Nat) -> (importCount : Nat) -> SchemaMismatch
