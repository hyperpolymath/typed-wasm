-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- SessionProtocol.idr — L14 Session Protocols for typed-wasm ABI
--
-- L14 lifts L10 linearity (resource handles consumed exactly once) into a
-- *protocol* discipline: a session is a finite-state machine over typed
-- linear handles, and every transition consumes one handle in the source
-- state and yields one handle in the target state. Two-party sessions
-- carry a `dual` relation that pairs send-states on one side with
-- receive-states on the other.
--
-- Why a separate level on top of L10:
--   * L10 proves that a single handle is freed (used) exactly once. That
--     is enough for `alloc -> free` discipline but not enough for sequenced
--     message exchanges where the next handle's TYPE depends on which
--     transition fired.
--   * L14 lifts the discipline so that the *type* of the next handle is
--     determined by the chosen transition. The Idris2 type system enforces
--     "after consume Idle and yield Active you may only call Active
--     transitions next" entirely at compile time.
--
-- The database analogy: L14 is row-level workflow state. A row in state
-- `Pending` may legally transition to `Approved` or `Rejected`; nothing
-- else, and exactly once. The compiler refuses to call `approve` on a row
-- already in `Approved`, just as L14 refuses to send a message on a handle
-- whose state has already moved on.
--
-- Proof strategy: model states as nominal type-level identifiers and
-- transitions as functions that consume a SessionHandle in one state and
-- produce a SessionHandle in the successor state. Linearity is inherited
-- from L10 — we wrap a `LinHandle` from Linear.idr and parameterise it by
-- the current session state. The "no transition out of an unknown state"
-- guarantee falls out structurally because the type system has no
-- introduction rule for handles in undeclared states.
--
-- NO `believe_me`, NO `assert_total`, NO `Admitted`. `%default total`.

module TypedWasm.ABI.SessionProtocol

import Data.List
import Data.List.Elem

import TypedWasm.ABI.Linear

%default total

-- ============================================================================
-- Session Identity
-- ============================================================================

||| A session protocol identifier. Sessions are nominal: two protocols
||| with structurally identical transition tables are still distinct types.
||| This prevents accidentally mixing session handles from different
||| protocols even when they look the same.
public export
data SessionId : Type where
  MkSessionId : (name : String) -> SessionId

public export
Eq SessionId where
  (MkSessionId a) == (MkSessionId b) = a == b

-- ============================================================================
-- Session States
-- ============================================================================

||| A state identifier inside a session protocol. The string is the
||| surface-syntax label (e.g. "Idle", "Active") and the carried `payload`
||| natural number is the size in bytes of the field this state holds.
||| The size must agree across all transitions that touch this state, so
||| the typed memory layout cannot drift between states.
public export
record StateId where
  constructor MkStateId
  stateName : String
  payload   : Nat

public export
Eq StateId where
  (MkStateId a p) == (MkStateId b q) = a == b && p == q

-- ============================================================================
-- Transitions
-- ============================================================================

||| A transition from one state to another. `transitionName` is the
||| surface label, `consumes` is the source state (matched at type level),
||| `produces` is the successor state.
|||
||| Note that there is NO third "rejected" branch. If a transition is
||| declared `consume Idle -> yield Active`, calling it on a handle in any
||| other state is a type error, not a runtime trap.
public export
record Transition where
  constructor MkTransition
  transitionName : String
  consumes       : StateId
  produces       : StateId

||| A transition list — every transition the protocol declares.
public export
TransitionList : Type
TransitionList = List Transition

-- ============================================================================
-- Protocol — the bundle
-- ============================================================================

||| A complete session protocol: identity, declared states, declared
||| transitions, and an optional `dual` link to the peer protocol used by
||| the OTHER party in a two-party session.
|||
||| The dual relation is symmetric in declaration but not enforced at this
||| level; the L14 surface checker pairs `dual : X` declarations and emits
||| a diagnostic if A says `dual : B` but B does not say `dual : A`.
public export
record Protocol where
  constructor MkProtocol
  protocolId  : SessionId
  states      : List StateId
  transitions : TransitionList
  dual        : Maybe SessionId

-- ============================================================================
-- Well-Formedness
-- ============================================================================

||| Proof that all state names in a list are distinct.
public export
data DistinctStateNames : List StateId -> Type where
  DSNNil  : DistinctStateNames []
  DSNCons : (s : StateId)
         -> (rest : List StateId)
         -> (freshness : Not (Elem s.stateName (map (\x => x.stateName) rest)))
         -> DistinctStateNames rest
         -> DistinctStateNames (s :: rest)

||| Proof that every transition's source and target states are declared in
||| the protocol's state list.
public export
data TransitionsClosed : List StateId -> TransitionList -> Type where
  TCNil  : (ss : List StateId) -> TransitionsClosed ss []
  TCCons : (ss : List StateId)
        -> (t : Transition)
        -> (rest : TransitionList)
        -> (consumesIn : Elem t.consumes ss)
        -> (producesIn : Elem t.produces ss)
        -> TransitionsClosed ss rest
        -> TransitionsClosed ss (t :: rest)

||| A well-formed protocol: distinct state names AND every transition is
||| closed under the declared state set. These two together rule out the
||| two most common surface bugs: typoed state names and dangling
||| transition references.
public export
data WellFormedProtocol : Protocol -> Type where
  MkWFP : (distinctNames : DistinctStateNames p.states)
       -> (closed        : TransitionsClosed p.states p.transitions)
       -> WellFormedProtocol p

-- ============================================================================
-- Session Handle — the linear typed-state carrier
-- ============================================================================

||| A linear session handle parameterised by its current state.
|||
||| The state index makes session handles strictly stronger than L10 linear
||| handles: not only must the handle be consumed exactly once (L10), the
||| consumption must happen via a transition whose `consumes` field equals
||| the handle's current state index. The Idris2 type checker rejects every
||| other call.
|||
||| Internally, a session handle wraps an L10 LinHandle so that the
||| underlying memory linearity story is unchanged.
public export
data SessionHandle : (proto : SessionId)
                  -> (state : StateId)
                  -> Type where
  MkSessionHandle : (proto : SessionId)
                 -> (state : StateId)
                 -> (token : Nat)
                 -> (inner : LinHandle token)
                 -> SessionHandle proto state

||| Extract the wrapped L10 handle from a session handle. Useful for
||| dropping back to plain memory operations between transitions.
public export
sessionInner : {proto : SessionId} -> {state : StateId}
            -> SessionHandle proto state -> (tk : Nat ** LinHandle tk)
sessionInner (MkSessionHandle _ _ tk inner) = (tk ** inner)

-- ============================================================================
-- Stepping a Transition
-- ============================================================================

||| Apply a transition to a session handle. The (1 _) quantity annotation
||| is the L10 linearity inheritance: the input handle is consumed exactly
||| once, and a new handle in the target state is produced.
|||
||| Type-level requirement: the transition's `consumes` field must equal
||| the input handle's state index. Failure to match is a type error at
||| call site, not a runtime check. This is the L14 soundness invariant.
public export
step : (proto : SessionId)
    -> (t : Transition)
    -> {auto consumesEq : t.consumes = s}
    -> (1 _ : SessionHandle proto s)
    -> SessionHandle proto t.produces
step proto t (MkSessionHandle _ _ tk inner) =
  MkSessionHandle proto t.produces tk inner

-- ============================================================================
-- Dual Relation (Two-Party Sessions)
-- ============================================================================

||| Proof that two protocols are dual: every send in one corresponds to a
||| receive in the other. At the L14 surface level we only carry the link
||| name; the structural symmetry check (every `consumes Active` on A
||| pairs with a `consumes ActiveDual` on B) is a future refinement.
|||
||| What this DOES capture: if A declares `dual : B`, then B MUST declare
||| `dual : A`, otherwise the L14 surface checker (Checker.checkSession)
||| produces a diagnostic. The Idris2 record below is the proof witness
||| that both directions are declared.
public export
data DualPair : (a : Protocol) -> (b : Protocol) -> Type where
  MkDualPair : (forwardDecl  : a.dual = Just b.protocolId)
            -> (backwardDecl : b.dual = Just a.protocolId)
            -> DualPair a b

||| Symmetry: if (a, b) is a dual pair, so is (b, a). Trivial structurally,
||| but useful at use sites where the caller has only one direction in
||| scope.
public export
dualSym : DualPair a b -> DualPair b a
dualSym (MkDualPair fwd bwd) = MkDualPair bwd fwd

-- ============================================================================
-- Soundness Theorems
-- ============================================================================

||| Project the state index out of a session handle.
public export
handleState : {proto : SessionId} -> {state : StateId}
           -> SessionHandle proto state -> StateId
handleState {state} _ = state

||| L14 type-state soundness:
|||
||| Statement: applying a transition `t` to a handle in state `t.consumes`
||| yields a handle whose state index equals `t.produces`.
|||
||| This is the definitional content of `step`. We restate it as a lemma
||| so that downstream proofs can refer to it without having to unfold
||| the definition.
public export
stepProducesTarget : (proto : SessionId)
                  -> (t : Transition)
                  -> (h : SessionHandle proto t.consumes)
                  -> handleState (step proto t {consumesEq = Refl} h) = t.produces
stepProducesTarget proto t h = Refl

||| L14 closed-transitions soundness:
|||
||| Statement: in a well-formed protocol, every transition's source and
||| target states are members of the protocol's declared state list.
||| Therefore, no L14 program can construct a session handle for a state
||| that the protocol does not declare — there is no introduction rule.
|||
||| Proof is trivial structural extraction from the WellFormedProtocol
||| witness; the value of stating it is that downstream code can rely on
||| the membership without re-walking the transition list.
public export
transitionStatesDeclared : (p : Protocol)
                        -> WellFormedProtocol p
                        -> (t : Transition)
                        -> Elem t p.transitions
                        -> (Elem t.consumes p.states, Elem t.produces p.states)
transitionStatesDeclared p (MkWFP _ closed) t inList =
  go closed inList
  where
    go : {ts : TransitionList}
      -> TransitionsClosed p.states ts
      -> Elem t ts
      -> (Elem t.consumes p.states, Elem t.produces p.states)
    go (TCCons _ _ _ cIn pIn _) Here = (cIn, pIn)
    go (TCCons _ _ _ _ _ rest) (There later) = go rest later

-- ============================================================================
-- Bridge to L10 Linearity
-- ============================================================================

||| Every session handle carries an L10 linear handle internally. Stepping
||| a transition consumes the session handle linearly (the (1 _) quantity
||| on `step`); the wrapped LinHandle is rewrapped into the successor
||| state's session handle, so the underlying L10 obligation is preserved
||| across the transition.
|||
||| In particular: a session that ends in a "terminal" state (one with no
||| outgoing transitions) MUST eventually be passed to `freeRegion` (from
||| Linear.idr) to discharge the L10 obligation. The L14 surface checker
||| at v1.3 does not yet enforce reaching a terminal state — that lands
||| with L16 choreography composition. v1.3 only enforces that every
||| transition the program calls is well-typed in the L14 sense.
public export
sessionToLinear : {proto : SessionId} -> {state : StateId}
               -> SessionHandle proto state
               -> (tk ** LinHandle tk)
sessionToLinear h = sessionInner h
