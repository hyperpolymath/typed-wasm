-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Choreography.idr — L16 Agent choreography composition for typed-wasm ABI
--
-- L16 composes three already-proven lower levels:
--   * L13 Module isolation (ModuleIsolation.idr)
--   * L14 Session protocols (SessionProtocol.idr)
--   * L15 Resource capabilities (ResourceCapabilities.idr)
--
-- The point of this module is NOT to re-prove those levels. Instead, L16
-- packages one proof witness per role and lifts that bundle to choreography-
-- level soundness for legal traces.
--
-- NO `believe_me`, NO `postulate`, NO `assert_total`, NO `Admitted`.
-- `%default total`.

module TypedWasm.ABI.Choreography

import Data.List
import Data.List.Elem

import TypedWasm.ABI.ModuleIsolation
import TypedWasm.ABI.SessionProtocol
import TypedWasm.ABI.ResourceCapabilities

%default total

-- ============================================================================
-- L16 Surface Core
-- ============================================================================

||| Nominal role identifier in a choreography.
public export
record AgentRole where
  constructor MkAgentRole
  roleName : String

public export
Eq AgentRole where
  (MkAgentRole a) == (MkAgentRole b) = a == b

||| Typed message edge: sender role, receiver role, payload type.
||| The constructor carries only a label; the payload type is tracked at type
||| level so message declarations remain typed without forcing value-level
||| payload terms into the choreography definition.
public export
data Message : (from : AgentRole) -> (to : AgentRole) -> (payload : Type) -> Type where
  MkMessage : (label : String) -> Message from to payload

||| Existential packaging for heterogeneous message payload types.
public export
record MessageDecl where
  constructor MkMessageDecl
  fromRole  : AgentRole
  toRole    : AgentRole
  payloadTy : Type
  msg       : Message fromRole toRole payloadTy

-- ============================================================================
-- Per-role realisation and lower-level composition witness
-- ============================================================================

||| One role's concrete lower-level realisation.
|||
||| `roleFunctionCaps` is a capability budget witness for the role's runtime
||| entrypoint in `moduleCaps`. L15 containment for this role is obtained by
||| citing `l15bSoundness`.
public export
record RoleRealisation where
  constructor MkRoleRealisation
  role               : AgentRole
  isolatedModule     : IsolatedModule
  sessionProtocol    : Protocol
  sessionWellFormed  : WellFormedProtocol sessionProtocol
  moduleCaps         : ModuleCaps
  roleFunctionCaps   : FunctionCaps moduleCaps

||| Per-role bundle of lower-level proof obligations (L13 + L14 + L15).
public export
record RoleRealisationWellFormed (r : RoleRealisation) where
  constructor MkRoleRealisationWellFormed
  l13Isolation         : WellFormedBoundaries r.isolatedModule.modId r.isolatedModule.boundaries
  l14SessionLinearity  : WellFormedProtocol r.sessionProtocol
  l15CapsContainment   : ContainedIn r.roleFunctionCaps.required (declared r.moduleCaps)

||| Build the per-role witness by CITING lower-level results:
|||   * L13: `isolatedModule.wellFormed`
|||   * L14: `sessionWellFormed`
|||   * L15: `l15bSoundness roleFunctionCaps`
public export
roleWitness : (r : RoleRealisation) -> RoleRealisationWellFormed r
roleWitness r =
  MkRoleRealisationWellFormed
    r.isolatedModule.wellFormed
    r.sessionWellFormed
    (l15bSoundness r.roleFunctionCaps)

||| List-level composition witness: every role in the choreography carries a
||| lower-level well-formedness witness.
public export
data AllRolesWellFormed : List RoleRealisation -> Type where
  AllWFNil  : AllRolesWellFormed []
  AllWFCons : {r : RoleRealisation}
           -> {rest : List RoleRealisation}
           -> RoleRealisationWellFormed r
           -> AllRolesWellFormed rest
           -> AllRolesWellFormed (r :: rest)

||| Convenience constructor: derive the list-level witness directly from the
||| role realisation list by reusing `roleWitness` for each role.
public export
deriveRoleWitnesses : (rs : List RoleRealisation) -> AllRolesWellFormed rs
deriveRoleWitnesses [] = AllWFNil
deriveRoleWitnesses (r :: rest) =
  AllWFCons (roleWitness r) (deriveRoleWitnesses rest)

-- ============================================================================
-- Choreography object
-- ============================================================================

||| L16 choreography declaration payload:
|||   * role list
|||   * typed message list
|||   * composition witness bundling L13/L14/L15 obligations per role
public export
record Choreography where
  constructor MkChoreography
  roles               : List AgentRole
  messages            : List MessageDecl
  realisations        : List RoleRealisation
  compositionWitness  : AllRolesWellFormed realisations

-- ============================================================================
-- Legal traces
-- ============================================================================

public export
data TraceStep : Type where
  TraceMessage : MessageDecl -> TraceStep

public export
Trace : Type
Trace = List TraceStep

||| A legal trace is a sequence of declared choreography messages.
public export
data LegalTrace : (c : Choreography) -> Trace -> Type where
  LegalTraceNil  : LegalTrace c []
  LegalTraceCons : {msg : MessageDecl}
                -> (declared : Elem msg c.messages)
                -> LegalTrace c rest
                -> LegalTrace c (TraceMessage msg :: rest)

-- ============================================================================
-- Choreography soundness (composition-only)
-- ============================================================================

||| Extracted L13 obligations for all roles.
public export
data AllIsolation : List RoleRealisation -> Type where
  IsolationNil  : AllIsolation []
  IsolationCons : {r : RoleRealisation}
               -> {rest : List RoleRealisation}
               -> WellFormedBoundaries r.isolatedModule.modId r.isolatedModule.boundaries
               -> AllIsolation rest
               -> AllIsolation (r :: rest)

||| Extracted L14 obligations for all roles.
public export
data AllSessionLinearity : List RoleRealisation -> Type where
  SessionNil  : AllSessionLinearity []
  SessionCons : {r : RoleRealisation}
             -> {rest : List RoleRealisation}
             -> WellFormedProtocol r.sessionProtocol
             -> AllSessionLinearity rest
             -> AllSessionLinearity (r :: rest)

||| Extracted L15 obligations for all roles.
public export
data AllCapabilityContainment : List RoleRealisation -> Type where
  CapabilityNil  : AllCapabilityContainment []
  CapabilityCons : {r : RoleRealisation}
                -> {rest : List RoleRealisation}
                -> ContainedIn r.roleFunctionCaps.required (declared r.moduleCaps)
                -> AllCapabilityContainment rest
                -> AllCapabilityContainment (r :: rest)

||| Build choreography-wide L13 obligations from the composition witness.
public export
collectIsolation : (rs : List RoleRealisation)
                -> AllRolesWellFormed rs
                -> AllIsolation rs
collectIsolation [] AllWFNil = IsolationNil
collectIsolation (_ :: rest) (AllWFCons wf restWf) =
  IsolationCons wf.l13Isolation (collectIsolation rest restWf)

||| Build choreography-wide L14 obligations from the composition witness.
public export
collectSessionLinearity : (rs : List RoleRealisation)
                       -> AllRolesWellFormed rs
                       -> AllSessionLinearity rs
collectSessionLinearity [] AllWFNil = SessionNil
collectSessionLinearity (_ :: rest) (AllWFCons wf restWf) =
  SessionCons wf.l14SessionLinearity (collectSessionLinearity rest restWf)

||| Build choreography-wide L15 obligations from the composition witness.
public export
collectCapabilityContainment : (rs : List RoleRealisation)
                            -> AllRolesWellFormed rs
                            -> AllCapabilityContainment rs
collectCapabilityContainment [] AllWFNil = CapabilityNil
collectCapabilityContainment (_ :: rest) (AllWFCons wf restWf) =
  CapabilityCons wf.l15CapsContainment (collectCapabilityContainment rest restWf)

||| L16 soundness payload:
|||   for a legal choreography trace, L13 isolation, L14 session linearity,
|||   and L15 capability containment all hold role-wise.
public export
record ChoreographySoundness (c : Choreography) where
  constructor MkChoreographySoundness
  l13Holds : AllIsolation c.realisations
  l14Holds : AllSessionLinearity c.realisations
  l15Holds : AllCapabilityContainment c.realisations

||| Main L16 theorem (composition-only):
||| For every legal trace of a choreography, the lower-level obligations hold.
||| The proof is by extraction from `compositionWitness`; no lower-level
||| theorem is re-proven here.
public export
traceSoundness : (c : Choreography)
              -> (tr : Trace)
              -> LegalTrace c tr
              -> ChoreographySoundness c
traceSoundness c tr legal =
  let _ = tr in
  let _ = legal in
  MkChoreographySoundness
    (collectIsolation c.realisations c.compositionWitness)
    (collectSessionLinearity c.realisations c.compositionWitness)
    (collectCapabilityContainment c.realisations c.compositionWitness)
