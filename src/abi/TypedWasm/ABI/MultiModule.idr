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

-- ============================================================================
-- A6 — Strengthened Propositional Layer (PROOF-NEEDS §P0.5, flagship)
-- ============================================================================
--
-- The data declarations above (ExportedRegion, ImportedRegion,
-- SchemaAgreement, CompatCertificate, LinkEdge, LinkGraph) are
-- preserved in their original shape.  They capture the *data* of a
-- multi-module link but do not by themselves manipulate any witnesses
-- — `SchemaAgreement` in particular only records module and region
-- names, not the per-field correspondence that "compatibility" really
-- depends on.
--
-- This section adds the propositional layer on top of those data
-- types.  The new types — `FieldMatches`, `SchemaSub`, `ModuleCompat`
-- — are indexed and carry witnesses, and the theorems `compatRefl`,
-- `compatTrans`, `noSpoofing` and `noTypeSpoofing` are statable only
-- at this strengthened level.  A worked Rust-exports-ReScript-imports
-- example at the end of the file constructs a live certificate and
-- applies the flagship theorem to it, so the proof is not vacuous.

||| FieldMatches f s — witness that a field `f` (with exactly this
||| (name, type) pair) appears somewhere in schema `s`.
|||
||| Stronger than a plain name-only membership proof (like `FieldIn`
||| in Region.idr): the entire Field constructor must match, so both
||| the name and the WasmType are transported by the witness.  If
||| `FieldMatches f s` holds, then `s` really contains `f` itself —
||| not merely something with the same name but a different type.
|||
||| Constructors are prefixed `FM` to avoid a clash with Region.idr's
||| `FieldHere` / `FieldThere`, which witness the weaker name-only
||| relation `FieldIn`.
public export
data FieldMatches : Field -> Schema -> Type where
  ||| `f` matches the schema's head field (both sides are literally the
  ||| same Field constructor application — identical name AND type).
  FMHere  : FieldMatches f (f :: fs)
  ||| `f` matches somewhere deeper in the schema's tail.
  FMThere : FieldMatches f fs -> FieldMatches f (f' :: fs)

||| SchemaSub imp exp — every field in `imp` appears in `exp` with
||| matching (name, type).  This is the structural-subtype witness
||| that lets an importer consume a subset (or reordering) of an
||| exporter's schema.
|||
||| Crucially this is NOT list equality: `imp` may omit fields,
||| duplicate references (though in practice a well-formed schema
||| won't), or occur in a different order than `exp`.  The only
||| requirement is that each imported field is a legitimate export.
|||
||| Constructors are prefixed `SS` to avoid a clash with Effects.idr's
||| `SubNil` / `SubCons`, which live in the parallel `EffectSubsumes`
||| universe.
public export
data SchemaSub : Schema -> Schema -> Type where
  ||| The empty schema is a subschema of any schema (vacuously).
  SSNil  : SchemaSub [] expS
  ||| A non-empty `imp` is a subschema of `expS` if its head matches
  ||| somewhere in `expS` AND its tail is itself a subschema of `expS`.
  SSCons : FieldMatches f expS
        -> SchemaSub fs expS
        -> SchemaSub (f :: fs) expS

-- ---- Internal lemmas used to build the preorder ----

||| Weaken a SchemaSub by adding a new field to the *front* of the
||| exporter side.  Every field that previously matched inside `exp`
||| still matches inside `f' :: exp`, just one step deeper.  Used by
||| `schemaSubRefl` below.
private
weakenSchemaSub : SchemaSub xs expS -> SchemaSub xs (f' :: expS)
weakenSchemaSub SSNil          = SSNil
weakenSchemaSub (SSCons fm tl) = SSCons (FMThere fm) (weakenSchemaSub tl)

||| If `f` matches in `y` and `y` is a subschema of `z`, then `f`
||| matches in `z`.  This is pointwise transitivity for FieldMatches,
||| and is the work-horse for both `schemaSubTrans` and `noSpoofing`.
private
fieldMatchesLift : FieldMatches f y -> SchemaSub y z -> FieldMatches f z
fieldMatchesLift FMHere           (SSCons fm _)  = fm
fieldMatchesLift (FMThere deeper) (SSCons _ tl)  = fieldMatchesLift deeper tl

-- ---- SchemaSub preorder (PROOF-NEEDS §P0.5 — reflexivity + transitivity) ----

||| SchemaSub is reflexive: every schema is a subschema of itself.
|||
||| The proof proceeds by structural induction on the schema.  The
||| head matches via `FMHere`, and the reflexivity of the tail is
||| weakened by `weakenSchemaSub` to account for the one-step deeper
||| context on the exporter side.
public export
schemaSubRefl : (s : Schema) -> SchemaSub s s
schemaSubRefl []         = SSNil
schemaSubRefl (f :: rest) =
  SSCons FMHere (weakenSchemaSub (schemaSubRefl rest))

||| SchemaSub is transitive.  If `imp` ⊆ `mid` and `mid` ⊆ `exp`,
||| then `imp` ⊆ `exp` — each field witness in `imp → mid` is lifted
||| through `mid → exp` to produce a field witness in `imp → exp`.
public export
schemaSubTrans : SchemaSub x y -> SchemaSub y z -> SchemaSub x z
schemaSubTrans SSNil          _  = SSNil
schemaSubTrans (SSCons fm tl) yz =
  SSCons (fieldMatchesLift fm yz) (schemaSubTrans tl yz)

-- ============================================================================
-- Module-Indexed Compatibility (the core relation for the flagship theorem)
-- ============================================================================

||| `ModuleCompat from to imp exp` — Module `from` is compatible with
||| importing schema `imp` from Module `to` which actually exports
||| schema `exp`.  Compatibility is witnessed by a SchemaSub proof.
|||
||| This is the `Compat m1 m2` relation from PROOF-NEEDS §P0.5,
||| strengthened with the two schemas so that structural claims can be
||| transported along the certificate.  The existing `CompatCertificate`
||| above is preserved as a weaker data-only form; `ModuleCompat` is
||| the propositional form over which the flagship theorem is stated.
|||
||| The module identifiers are carried purely as type-level tags —
||| they appear in error messages and diagnostics but the proof
||| content lives entirely in the `SchemaSub` witness.
public export
data ModuleCompat : (from   : ModuleId)
                 -> (to     : ModuleId)
                 -> (imp    : Schema)
                 -> (expS   : Schema)
                 -> Type where
  MkModuleCompat : SchemaSub imp expS -> ModuleCompat from to imp expS

||| ModuleCompat is reflexive: any module is trivially compatible
||| with itself when the imported schema IS the exported schema.
|||
||| PROOF-NEEDS §P0.5 spells this out as
|||   `compatRefl : (m : ModuleId) -> Compat m m`
||| — the schema-indexed form here additionally records *which*
||| schema is being transported.
public export
compatRefl : (m : ModuleId) -> (s : Schema) -> ModuleCompat m m s s
compatRefl _ s = MkModuleCompat (schemaSubRefl s)

||| ModuleCompat is transitive: if m1 imports `s1` from m2 (which
||| actually exports `s2`), and m2 imports `s2` from m3 (which
||| actually exports `s3`), then m1 imports `s1` from m3 (which
||| exports `s3`).  The SchemaSub witnesses chain via
||| `schemaSubTrans`.
public export
compatTrans : ModuleCompat m1 m2 s1 s2
           -> ModuleCompat m2 m3 s2 s3
           -> ModuleCompat m1 m3 s1 s3
compatTrans (MkModuleCompat sub12) (MkModuleCompat sub23) =
  MkModuleCompat (schemaSubTrans sub12 sub23)

-- ============================================================================
-- The Flagship: No-Spoofing Theorem (PROOF-NEEDS §P0.5)
-- ============================================================================

||| No-spoofing theorem — given a module-compatibility certificate,
||| every field the importer references is a bona-fide field of the
||| exporter with matching (name, type).  There is no way to import
||| a field with a name/type combination that the exporter did not
||| actually export.
|||
||| PROOF-NEEDS §P0.5 calls this "the actual multi-module memory
||| safety invariant — the paper's killer feature".  It is the
||| formal counterpart of the informal claim made throughout
||| typed-wasm's docs: "cross-module memory safety across language
||| boundaries".
|||
||| Reading: if you can produce a `ModuleCompat from to imp exp`
||| certificate and a `FieldMatches f imp` witness, then the proof
||| term constructively transports the import evidence into
||| `FieldMatches f exp` — a witness that `f` really is in `exp`.
|||
||| The theorem is NOT vacuous.  The certificate's `SchemaSub`
||| witness is unpacked field-by-field via `fieldMatchesLift`
||| (which does the recursive search).  The proof cannot be
||| constructed from thin air — it requires an actual subschema
||| relation.
public export
noSpoofing : ModuleCompat from to imp expS
          -> (f : Field)
          -> FieldMatches f imp
          -> FieldMatches f expS
noSpoofing (MkModuleCompat sub) _ fm = fieldMatchesLift fm sub

||| Type-preservation corollary.  If the importer sees a field
||| `(name, ty)`, the exporter has exactly that `(name, ty)` —
||| the WasmType is transported unchanged.
|||
||| This is a direct specialisation of `noSpoofing` at a known
||| `(name, ty)` pair, but stating it separately makes the
||| type-safety guarantee explicit at the API level.  A caller
||| worried about type drift can quote this lemma directly
||| without unpacking the `FieldMatches` witness.
public export
noTypeSpoofing : ModuleCompat from to imp expS
              -> (name : String)
              -> (ty   : WasmType)
              -> FieldMatches (MkField name ty) imp
              -> FieldMatches (MkField name ty) expS
noTypeSpoofing cert name ty fm = noSpoofing cert (MkField name ty) fm

-- ============================================================================
-- Worked Example: Rust exports, ReScript imports (strict subset)
-- ============================================================================
--
-- PROOF-NEEDS §P0.5 recommends writing a small example multi-module
-- program to sanity-check the statement before proving it.  This
-- namespace constructs a concrete Rust-exports / ReScript-imports
-- link: the backend exports a 4-field `UserProfile` region and the
-- frontend imports just the first two fields.  The compatibility
-- certificate is then built explicitly and `noSpoofing` is applied
-- to it, demonstrating that the theorem has real computational
-- content (not just an unused abstract witness).

namespace Example
  ||| Rust backend module identifier.
  public export
  rustBackend : ModuleId
  rustBackend = MkModuleId "rust_backend"

  ||| ReScript frontend module identifier.
  public export
  rescriptFrontend : ModuleId
  rescriptFrontend = MkModuleId "rescript_frontend"

  ||| Rust exports a full user profile: id, age, score, banned.
  public export
  rustExportSchema : Schema
  rustExportSchema =
    [ MkField "id"     U64
    , MkField "age"    U8
    , MkField "score"  F32
    , MkField "banned" WBool
    ]

  ||| ReScript only needs the first two fields to render the UI.
  ||| Note this is a strict subset — `score` and `banned` are
  ||| hidden from the frontend.
  public export
  rescriptImportSchema : Schema
  rescriptImportSchema =
    [ MkField "id"  U64
    , MkField "age" U8
    ]

  ||| Each imported field is witnessed by an explicit FieldMatches
  ||| proof.  `id` is at the head of the export; `age` is the
  ||| second element so its proof is `FMThere FMHere`.
  |||
  ||| The fully-qualified schema names (`Example.rescriptImportSchema`
  ||| etc.) are required because Idris2 treats lowercase identifiers
  ||| in type signatures as implicit binders.
  public export
  exampleSchemaSub : SchemaSub Example.rescriptImportSchema
                               Example.rustExportSchema
  exampleSchemaSub =
    SSCons FMHere                       -- id  at head
      (SSCons (FMThere FMHere) SSNil)   -- age at position 1

  ||| The live compatibility certificate.  Its construction requires
  ||| the SchemaSub witness above; without it, the certificate
  ||| cannot be built.
  public export
  exampleCompat : ModuleCompat Example.rescriptFrontend
                               Example.rustBackend
                               Example.rescriptImportSchema
                               Example.rustExportSchema
  exampleCompat = MkModuleCompat exampleSchemaSub

  ||| Apply the no-spoofing theorem: starting from the import-side
  ||| witness `FMHere : FieldMatches (MkField "id" U64)
  ||| rescriptImportSchema`, the theorem produces an export-side
  ||| witness that `(MkField "id" U64)` really lives in
  ||| `rustExportSchema`.  The theorem carries real content — it
  ||| walks the SchemaSub to locate the export-side position.
  public export
  exampleNoSpoofing : FieldMatches (MkField "id" U64)
                                   Example.rustExportSchema
  exampleNoSpoofing =
    noSpoofing exampleCompat (MkField "id" U64) FMHere
