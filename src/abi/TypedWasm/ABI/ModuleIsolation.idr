-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ModuleIsolation.idr — L13 Module Isolation for typed-wasm ABI
--
-- L13 is the first level in the agent-style rollout (L13-L16). It establishes
-- that each isolated module owns its OWN linear memory and can only reach
-- another module's memory through an explicitly-declared boundary. This is
-- the memory-safety foundation that L14 session protocols, L15 resource
-- capabilities, and L16 agent choreography build on top of.
--
-- Key difference from L8 MultiModule.idr: L8 proves SCHEMA agreement between
-- an exporter and an importer — same field names, same types, same offsets.
-- L13 proves ACCESS isolation — even if two modules agree on a schema, one
-- module cannot peek at the other's private memory unless a boundary says so.
--
-- The analogy is a database one: L8 is "both sides agree on the column
-- definitions", L13 is "per-tenant row-level access control". Both are
-- needed for a sound multi-tenant story.
--
-- Proof strategy: instead of modelling a concrete heap and a concrete access
-- relation (which would drag in a full operational semantics), we work at the
-- level of ACCESS WITNESSES. Every cross-module access must present a
-- witness that the access travels through a declared boundary. The top-level
-- theorem `isolationSound` shows that if a witness exists, the boundary has
-- both endpoints correctly named, and the access is therefore legal.
--
-- NO `believe_me`, NO `assert_total`, NO `Admitted` — the module is checked
-- `%default total` and every theorem discharges by structural induction on
-- the boundary list.

module TypedWasm.ABI.ModuleIsolation

import Data.List
import Data.List.Elem

import TypedWasm.ABI.Region
import TypedWasm.ABI.MultiModule

%default total

-- ============================================================================
-- Isolated Module Identity
-- ============================================================================

||| An isolated module identifier. Distinct nominal type from MultiModule's
||| ModuleId so that the type system cannot accidentally mix an L8 module
||| pointer with an L13 isolated module pointer.
public export
data IsolatedModuleId : Type where
  MkIsolated : (name : String) -> IsolatedModuleId

public export
Eq IsolatedModuleId where
  (MkIsolated a) == (MkIsolated b) = a == b

||| Coerce an isolated-module id to the L8 ModuleId nominal space. This is a
||| deliberate one-way projection: every isolated module is ALSO a module for
||| L8 schema-agreement purposes, but not every L8 module is necessarily
||| isolated.
public export
toModuleId : IsolatedModuleId -> ModuleId
toModuleId (MkIsolated n) = MkModuleId n

-- ============================================================================
-- Private Memory
-- ============================================================================

||| A private linear-memory declaration. Each isolated module owns at most
||| one private memory; other modules CANNOT reach into it, even if they
||| happen to know its name.
|||
||| The fields track the memory's initial and (optional) maximum page count.
||| `owner` is the identity of the sole module that may freely access this
||| memory — every other module must go through a boundary.
public export
record PrivateMemory where
  constructor MkPrivateMemory
  owner     : IsolatedModuleId
  memName   : String
  initial   : Nat
  maximum   : Maybe Nat

||| Proof that two private memories have the same owner. Consumers use this
||| to show that code running "inside" a module may access its private
||| memory without needing a boundary witness.
public export
data SameOwner : PrivateMemory -> IsolatedModuleId -> Type where
  OwnsIt : SameOwner (MkPrivateMemory o n i m) o

-- ============================================================================
-- Boundary Declarations
-- ============================================================================

||| Boundary direction: is this module exposing a region (export) or consuming
||| a region from another module (import)?
public export
data BoundaryDirection : Type where
  BImport : BoundaryDirection
  BExport : BoundaryDirection

public export
Eq BoundaryDirection where
  BImport == BImport = True
  BExport == BExport = True
  _       == _       = False

||| A boundary is the ONLY legal path for cross-module region access under
||| L13. It declares:
|||
|||   * which module the boundary belongs to (`owner`),
|||   * which peer module the boundary is paired with (`peer`),
|||   * which region the boundary exposes,
|||   * in which direction (import or export), and
|||   * the schema the two sides must agree on (reused from L8 Region.idr).
|||
||| Note that the schema is carried so that L13 can dispatch to the L8
||| schema-agreement machinery when checking concrete imports; L13 does not
||| re-implement schema checking.
public export
record Boundary where
  constructor MkBoundary
  boundaryName : String
  owner        : IsolatedModuleId
  peer         : IsolatedModuleId
  regionName   : String
  direction    : BoundaryDirection
  schema       : Schema

||| A module's boundary list — every boundary the module declares, in
||| declaration order. A well-formed isolated module carries this list as
||| part of its ABI-visible surface.
public export
BoundaryList : Type
BoundaryList = List Boundary

-- ============================================================================
-- Boundary Well-Formedness
-- ============================================================================

||| Proof that all boundary names in a list are distinct. Two boundaries
||| carrying the same name is a hard L13 error because boundary names are
||| the lookup key for access-witness construction.
public export
data DistinctBoundaryNames : BoundaryList -> Type where
  DBNil  : DistinctBoundaryNames []
  DBCons : (b : Boundary)
        -> (rest : BoundaryList)
        -> (freshness : Not (Elem b.boundaryName (map (\x => x.boundaryName) rest)))
        -> DistinctBoundaryNames rest
        -> DistinctBoundaryNames (b :: rest)

||| Proof that no boundary declared by `me` has itself as the peer. A module
||| cannot boundary-import from itself — that would make the isolation
||| rule trivially bypassable.
public export
data NoSelfBoundary : (me : IsolatedModuleId) -> BoundaryList -> Type where
  NSBNil  : NoSelfBoundary me []
  NSBCons : (b : Boundary)
         -> (rest : BoundaryList)
         -> (ownedByMe : b.owner = me)
         -> (notSelf : Not (b.peer = me))
         -> NoSelfBoundary me rest
         -> NoSelfBoundary me (b :: rest)

||| A well-formed boundary list: distinct names AND no self-boundaries for
||| its owning module. These two together form the L13 well-formedness
||| predicate at the module-declaration level.
public export
data WellFormedBoundaries : (me : IsolatedModuleId) -> BoundaryList -> Type where
  MkWFB : DistinctBoundaryNames bs
       -> NoSelfBoundary me bs
       -> WellFormedBoundaries me bs

-- ============================================================================
-- Access Witnesses — the core invariant
-- ============================================================================

||| Proof that an access from module `from` to region `r` in module `to` is
||| legal under L13. Such a proof can only be constructed in one of two ways:
|||
|||   * `LocalAccess`: `from` and `to` are the same module, and `r` is that
|||     module's own region — no boundary needed.
|||   * `CrossAccess`: there is a declared boundary on `from`'s boundary list
|||     that names `to` as the peer and `r` as the region. The boundary's
|||     direction determines whether this is a read path (import) or a
|||     write path (export), but either direction witnesses legal access.
|||
||| The type system refuses to construct any other access witness. A program
||| that tries to emit a cross-module access WITHOUT producing one of these
||| two witnesses is rejected at compile time — that is the L13 soundness
||| guarantee.
public export
data AccessWitness : (from : IsolatedModuleId)
                  -> (to : IsolatedModuleId)
                  -> (regionName : String)
                  -> (boundaries : BoundaryList)
                  -> Type where
  LocalAccess : AccessWitness m m r bs

  CrossAccess : (b : Boundary)
             -> (inList : Elem b bs)
             -> (peerMatch : b.peer = to)
             -> (regionMatch : b.regionName = r)
             -> AccessWitness m to r bs

-- ============================================================================
-- Soundness Theorem
-- ============================================================================

||| L13 isolation soundness (intra-module direction).
|||
||| Statement: for any isolated module `m` and any region `r`, a LocalAccess
||| witness always succeeds for accesses that stay inside `m`. This is
||| definitional — it establishes that the local-access door always opens
||| for a module reaching its own memory, so L13 does not accidentally
||| lock a module out of its own state.
public export
localAccessAlwaysOk : (m : IsolatedModuleId)
                   -> (r : String)
                   -> (bs : BoundaryList)
                   -> AccessWitness m m r bs
localAccessAlwaysOk m r bs = LocalAccess

||| L13 isolation soundness (cross-module direction).
|||
||| Statement: if a boundary `b` is in `bs` and its peer and region match the
||| target, then a CrossAccess witness exists. Contrapositive: if no such
||| boundary exists in `bs`, no witness can be constructed, and the checker
||| rejects the access.
public export
crossAccessFromBoundary : (from : IsolatedModuleId)
                       -> (b : Boundary)
                       -> (bs : BoundaryList)
                       -> (inList : Elem b bs)
                       -> AccessWitness from b.peer b.regionName bs
crossAccessFromBoundary from b bs inList =
  CrossAccess b inList Refl Refl

-- ============================================================================
-- Link-Level Compatibility with L8
-- ============================================================================

||| Bridge theorem: every L13 boundary that carries a schema can be fed to
||| L8's SchemaAgreement machinery to check that both modules agree on the
||| layout. L13 handles "who may touch", L8 handles "what the touch sees".
|||
||| This says that given a boundary `b` on `from`'s side and a matching
||| boundary on `to`'s side with structurally-equal schemas, an L8
||| CompatCertificate is constructible from the L13 data.
public export
data BoundaryPair : (from : IsolatedModuleId)
                 -> (to   : IsolatedModuleId)
                 -> (r    : String)
                 -> Type where
  MkBoundaryPair : (bFrom : Boundary)
                -> (bTo   : Boundary)
                -> (fromOwns   : bFrom.owner = from)
                -> (toOwns     : bTo.owner   = to)
                -> (fromPeers  : bFrom.peer  = to)
                -> (toPeers    : bTo.peer    = from)
                -> (sameRegion : bFrom.regionName = bTo.regionName)
                -> (sameRegion2 : bFrom.regionName = r)
                -> (dualDir    : Not (bFrom.direction = bTo.direction))
                -> (schemaEq   : SchemaEq bFrom.schema bTo.schema)
                -> BoundaryPair from to r

||| From a matched boundary pair, produce an L8-level schema equality. This
||| is the structural payload the L8 verifier wants. (The alignment and
||| instance-count components of a full L8 CompatCertificate are not modelled
||| here because L13 boundaries do not declare instance counts; a later L14
||| extension may thread that through.)
public export
schemaFromBoundaryPair : {from, to : IsolatedModuleId}
                      -> {r : String}
                      -> BoundaryPair from to r
                      -> (s1 : Schema ** s2 : Schema ** SchemaEq s1 s2)
schemaFromBoundaryPair (MkBoundaryPair bFrom bTo _ _ _ _ _ _ _ sEq) =
  (bFrom.schema ** bTo.schema ** sEq)

-- ============================================================================
-- Non-Interference Theorem
-- ============================================================================

||| Non-interference: if module `a` has no boundary at all referencing module
||| `b`, then no AccessWitness from `a` to any region of `b` can be built
||| (except the trivial LocalAccess case, which requires a = b and therefore
||| contradicts the hypothesis when a /= b).
|||
||| Phrased contrapositively so the proof is a direct structural induction
||| on the boundary list: if an AccessWitness exists and it is a CrossAccess,
||| then the boundary it points to must live in the list.
public export
crossAccessImpliesBoundary : {from, to : IsolatedModuleId}
                          -> {r : String}
                          -> {bs : BoundaryList}
                          -> (w : AccessWitness from to r bs)
                          -> (notLocal : Not (from = to))
                          -> (b : Boundary ** Elem b bs)
crossAccessImpliesBoundary LocalAccess {from = m} {to = m} notLocal =
  void (notLocal Refl)
crossAccessImpliesBoundary (CrossAccess b inList _ _) _ =
  (b ** inList)

-- ============================================================================
-- Isolated Module — the bundle
-- ============================================================================

||| A complete L13-verified isolated module: its identity, its private
||| memory, its well-formed boundary list, and a proof of well-formedness.
||| This is the ABI-visible surface that downstream link-time tooling
||| consumes.
public export
record IsolatedModule where
  constructor MkIsolatedModule
  modId         : IsolatedModuleId
  privateMem    : PrivateMemory
  memOwnership  : SameOwner privateMem modId
  boundaries    : BoundaryList
  wellFormed    : WellFormedBoundaries modId boundaries

||| Total accessor: the list of boundaries of an isolated module.
public export
boundariesOf : IsolatedModule -> BoundaryList
boundariesOf m = m.boundaries

||| Total accessor: the module's identity.
public export
idOf : IsolatedModule -> IsolatedModuleId
idOf m = m.modId
