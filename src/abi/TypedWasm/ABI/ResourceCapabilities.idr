-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ResourceCapabilities.idr — L15 Resource Capabilities for typed-wasm ABI
--
-- L15 elevates the `caps:` sub-clause of the v1.1 split-effects form from
-- an opaque name list into a load-bearing capability lattice. Each capability
-- names an external resource (e.g. read_file, web_fetch, gpio_pin_4) that
-- a function may need in order to run. The capability system is ORTHOGONAL
-- to the L8 memory-effect system — they form two independent lattices whose
-- obligations are checked independently.
--
-- Three invariants, each named at the Zig/ReScript surface as L15-A..L15-C:
--
--   L15-A  (Distinct)     A module declares each capability at most once.
--   L15-B  (Well-scoped)  A function's `caps:` set must be a subset of the
--                         enclosing module's declared capability set — you
--                         cannot require a capability that was never
--                         declared, because the grant point would be
--                         nowhere.
--   L15-C  (Monotone)     If function F calls function G, then F's declared
--                         capability set must INCLUDE G's declared capability
--                         set. Capability requirements propagate upwards
--                         along the call graph. A caller must already hold
--                         every capability the callee needs.
--
-- The L15-C rule is the key safety property: a function cannot "launder"
-- capabilities by calling a function that requires them. If main() doesn't
-- declare `net`, it cannot transitively reach any function that does.
--
-- Why orthogonal to memory effects: memory effects (Read/Write/Alloc/Free)
-- track INTERNAL state transitions on linear memory. Capabilities track
-- access to EXTERNAL resources that cross the wasm boundary. A pure function
-- over linear memory has no capabilities even if its memory effects are
-- maximal; an effectful external-resource function may be pure in memory but
-- capability-heavy. Conflating them loses information the checker needs.
--
-- Proof strategy: model capabilities as nominal type-level identifiers
-- (Strings wrapped in a newtype). A module declares a CapabilitySet (list of
-- names with DistinctCaps proof). A function declares a RequiredCaps set
-- that must be ContainedIn the module's set. Call-graph soundness is
-- expressed as CallCompatible: the caller's declared set contains the
-- callee's declared set. Each relation has a constructive witness, so
-- misuse cannot be proved and correct use carries machine-checked evidence.
--
-- NO `believe_me`, NO `postulate`, NO `assert_total`, NO `Admitted`.
-- `%default total`.

module TypedWasm.ABI.ResourceCapabilities

import Data.List
import Data.List.Elem

import TypedWasm.ABI.Effects

%default total

-- ============================================================================
-- Capability Identity
-- ============================================================================

||| A capability name. The surface syntax writes bare identifiers like
||| `read_file`; internally we wrap the name in a one-field record so the
||| type system refuses to confuse capability names with arbitrary strings,
||| memory-effect labels, or region names.
public export
record CapabilityName where
  constructor MkCapabilityName
  capName : String

public export
Eq CapabilityName where
  (MkCapabilityName a) == (MkCapabilityName b) = a == b

public export
Show CapabilityName where
  show (MkCapabilityName n) = n

-- ============================================================================
-- Capability Set
-- ============================================================================

||| A capability set is an ordered list of capability names. Well-formed
||| capability sets are DISTINCT — no name appears twice. The distinctness
||| proof is kept separate from the list itself so that list operations
||| (append, filter, map) can reuse the ordinary List type without wrapping.
public export
CapabilitySet : Type
CapabilitySet = List CapabilityName

||| The empty capability set — a function that needs no external resources.
public export
emptyCaps : CapabilitySet
emptyCaps = []

-- ============================================================================
-- L15-A: Distinctness
-- ============================================================================

||| Proof that a capability set contains no duplicates. Mirrors the
||| Distinct patterns used in ModuleIsolation.idr and SessionProtocol.idr
||| so that all three levels share a single surface idiom.
public export
data DistinctCaps : CapabilitySet -> Type where
  DistinctNil  : DistinctCaps []
  DistinctCons : {c : CapabilityName}
              -> {rest : CapabilitySet}
              -> (notThere : Not (Elem c rest))
              -> (restDistinct : DistinctCaps rest)
              -> DistinctCaps (c :: rest)

-- ============================================================================
-- L15-B: Well-scoped containment
-- ============================================================================

||| Proof that every capability in `required` is also in `declared`. This is
||| the subset relation, constructively witnessed. The checker uses this to
||| enforce that a function's declared `caps:` set is a subset of the
||| enclosing module's declared capability set (L15-B) and that a call site
||| is monotone (L15-C).
|||
||| ContainedIn is the core L15 judgement and is used twice:
|||   * L15-B — module has at least all capabilities the function requires
|||   * L15-C — caller has at least all capabilities the callee requires
public export
data ContainedIn : (required : CapabilitySet) -> (declared : CapabilitySet) -> Type where
  ||| The empty set is contained in any set.
  ContainedNil  : ContainedIn [] declared
  ||| If `c` is in `declared` and `rest` is contained in `declared`, the
  ||| whole required set `c :: rest` is contained.
  ContainedCons : {c : CapabilityName}
               -> {restReq : CapabilitySet}
               -> {declared : CapabilitySet}
               -> (here  : Elem c declared)
               -> (rest : ContainedIn restReq declared)
               -> ContainedIn (c :: restReq) declared

||| Containment is reflexive: every set contains itself.
public export
containedRefl : (cs : CapabilitySet) -> ContainedIn cs cs
containedRefl [] = ContainedNil
containedRefl (x :: xs) =
  ContainedCons Here (containedWeaken (containedRefl xs))
  where
    containedWeaken : ContainedIn cs xs -> ContainedIn cs (x :: xs)
    containedWeaken ContainedNil = ContainedNil
    containedWeaken (ContainedCons h r) =
      ContainedCons (There h) (containedWeaken r)

||| Helper: if `c ∈ ys` and `ys ⊆ zs`, then `c ∈ zs`. Promoted to
||| top level so the elaborator can see the `ys` indexing clearly
||| when pattern-matching.
public export
elemContained : {c : CapabilityName}
             -> {ys, zs : CapabilitySet}
             -> Elem c ys
             -> ContainedIn ys zs
             -> Elem c zs
elemContained Here      (ContainedCons h _) = h
elemContained (There p) (ContainedCons _ r) = elemContained p r

||| Containment is transitive: if A ⊆ B and B ⊆ C then A ⊆ C.
|||
||| The call-graph argument is: G's required caps are contained in G's
||| declared caps (trivially, by reflexivity); G's declared caps are
||| contained in F's declared caps (because F calls G, L15-C); therefore
||| G's required caps are contained in F's declared caps — the caller
||| covers the callee's needs.
public export
containedTrans : {xs, ys, zs : CapabilitySet}
              -> ContainedIn xs ys
              -> ContainedIn ys zs
              -> ContainedIn xs zs
containedTrans ContainedNil         _ = ContainedNil
containedTrans (ContainedCons h r) byz =
  ContainedCons (elemContained h byz) (containedTrans r byz)

-- ============================================================================
-- L15-C: Call-graph monotonicity
-- ============================================================================

||| A call-site witness: the caller's declared capability set contains the
||| callee's declared capability set. The Idris2 type system enforces this
||| structurally — a CallCompatible value can only be constructed when the
||| containment holds.
public export
data CallCompatible : (caller : CapabilitySet) -> (callee : CapabilitySet) -> Type where
  MkCallCompatible : (contained : ContainedIn callee caller)
                  -> CallCompatible caller callee

||| Self-calls are always compatible.
public export
selfCallCompatible : (cs : CapabilitySet) -> CallCompatible cs cs
selfCallCompatible cs = MkCallCompatible (containedRefl cs)

||| Call compatibility composes: if F can call G and G can call H, then
||| F can call H transitively. This is the key soundness lemma for
||| closure of the call graph under L15-C.
public export
callCompose : {f, g, h : CapabilitySet}
           -> CallCompatible f g
           -> CallCompatible g h
           -> CallCompatible f h
callCompose (MkCallCompatible fg) (MkCallCompatible gh) =
  MkCallCompatible (containedTrans gh fg)

-- ============================================================================
-- Module-level Capability Declaration
-- ============================================================================

||| A module's declared capability budget. Carries the name list plus an
||| L15-A distinctness proof. Functions declared in this module may require
||| any subset of `declared` and may call any function whose required set is
||| contained in their own declared set.
public export
record ModuleCaps where
  constructor MkModuleCaps
  declared : CapabilitySet
  distinct : DistinctCaps declared

||| The empty module — no capabilities declared, no external resources
||| reachable.
public export
emptyModuleCaps : ModuleCaps
emptyModuleCaps = MkModuleCaps [] DistinctNil

-- ============================================================================
-- Function Capability Requirement
-- ============================================================================

||| A function's capability requirement, witnessed against its enclosing
||| module. The L15-B proof is BAKED IN: you cannot construct a
||| FunctionCaps value unless its `required` set is contained in `owner`.
|||
||| This is the "can the compiler emit a typed-wasm function with this
||| signature?" question. The answer is `yes` iff you can hand the compiler
||| a ContainedIn witness for the function's caps against the module's caps.
public export
record FunctionCaps (owner : ModuleCaps) where
  constructor MkFunctionCaps
  required  : CapabilitySet
  scoped    : ContainedIn required (declared owner)

||| Construct a pure-capability function: one that needs no external
||| resources. Trivially well-scoped inside any module.
public export
pureFunctionCaps : (owner : ModuleCaps) -> FunctionCaps owner
pureFunctionCaps owner = MkFunctionCaps [] ContainedNil

-- ============================================================================
-- Call Site Well-Formedness
-- ============================================================================

||| A well-formed call site inside a module: the caller's FunctionCaps
||| record has `required` containing the callee's `required`. Builds on
||| L15-C monotonicity — if a call site is well-formed, the capability
||| budget of the caller covers the callee's needs.
public export
data WellFormedCall : (owner : ModuleCaps)
                   -> (caller : FunctionCaps owner)
                   -> (callee : FunctionCaps owner)
                   -> Type where
  MkWellFormedCall : {owner : ModuleCaps}
                  -> {caller : FunctionCaps owner}
                  -> {callee : FunctionCaps owner}
                  -> (compat : CallCompatible caller.required callee.required)
                  -> WellFormedCall owner caller callee

||| Self-calls are always well-formed, as a direct consequence of
||| `selfCallCompatible`.
public export
selfCallWellFormed : {owner : ModuleCaps}
                  -> (fc : FunctionCaps owner)
                  -> WellFormedCall owner fc fc
selfCallWellFormed fc = MkWellFormedCall (selfCallCompatible fc.required)

-- ============================================================================
-- Bridge to L8 Memory Effects — orthogonality theorem
-- ============================================================================
--
-- L15 is ORTHOGONAL to L8 memory effects. The proof of orthogonality is
-- that neither level's judgements mention the other's labels. We make this
-- explicit here as a pair type: a function's complete obligation is a
-- (MemEffect-set, CapabilitySet) pair, and the two halves are checked
-- independently by their respective level judgements.

||| The complete effect budget of a typed-wasm function: memory effects
||| (L8) and capabilities (L15) live in independent lattices. A function
||| satisfies its typing obligation if the memory-effect subsumption holds
||| AND the capability containment holds — each half is a separate proof
||| and neither half affects the other.
public export
record FullEffectBudget (owner : ModuleCaps) where
  constructor MkFullEffectBudget
  memoryEffects : EffectSet
  capability    : FunctionCaps owner

||| The pure budget: no memory effects, no capabilities.
public export
pureBudget : (owner : ModuleCaps) -> FullEffectBudget owner
pureBudget owner = MkFullEffectBudget [] (pureFunctionCaps owner)

-- ============================================================================
-- Soundness Theorems
-- ============================================================================

||| L15-B soundness: if a FunctionCaps was successfully constructed, then
||| its required set really is contained in the module's declared set.
||| This is essentially "look at the field" — we state it as a theorem so
||| downstream proofs can cite `l15bSoundness` by name.
public export
l15bSoundness : {owner : ModuleCaps}
             -> (fc : FunctionCaps owner)
             -> ContainedIn fc.required (declared owner)
l15bSoundness fc = fc.scoped

||| L15-C soundness: if a call site is well-formed, then the caller's
||| required set contains the callee's required set.
public export
l15cSoundness : {owner : ModuleCaps}
             -> {caller, callee : FunctionCaps owner}
             -> WellFormedCall owner caller callee
             -> ContainedIn callee.required caller.required
l15cSoundness (MkWellFormedCall (MkCallCompatible c)) = c

||| Full soundness: at a well-formed call site, the callee's required
||| capabilities are contained in the MODULE's declared capability set,
||| not merely in the caller's required set. This follows by transitivity:
||| callee.required <= caller.required (L15-C) and
||| caller.required <= owner.declared  (L15-B).
||| Hence callee.required <= owner.declared.
public export
callReachesModule : {owner : ModuleCaps}
                 -> {caller, callee : FunctionCaps owner}
                 -> WellFormedCall owner caller callee
                 -> ContainedIn callee.required (declared owner)
callReachesModule {caller} {callee} wf =
  containedTrans (l15cSoundness wf) (l15bSoundness caller)
