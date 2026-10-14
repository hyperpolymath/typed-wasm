-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- KCut.idr — K-CUT-LOSS for graded choreographies, parametric in the grade
-- kernel's resource algebra.
--
--   kcutLoss : gradeAt p (cutGlobal gl c) = lgrade (cutLocal (proj p gl) (cutproj p c))
--
-- "The global accumulation over a protocol up to a consistent cut, restricted
-- to party p, equals the grade p reads on its own local timeline up to the
-- projected cut."  Assembled, as upstream, from three lemmas:
--   projCut          projection commutes with cutting (no algebra laws)
--   gradeProj        restricted global grade = grade of the projection, for
--                    projectable protocols (uses only seqUnitL and altIdem)
--   cutProjectable   a consistent cut of any protocol is projectable
--
-- PROVENANCE.  Ported and re-proved from hyperpolymath/choreographic-types
--   src/Choreographic/{Party,Global,Local,Projection,KCut,Instances}.agda
--   @ edb784a7d26c276c2abfa8399b773d346dbb101e
-- (fetched by scripts/fetch-siblings.sh), there parametric in
-- resource-algebra's record, here in TypedWasm.ABI.ResourceAlgebra's
-- interface.  Agda is the proof kernel; these Idris2 proofs are the ABI
-- layer's own.  Statement correspondence: ASSUMED (port-and-reprove).
-- Upstream claim map: K-1 kcutLoss, K-2 projCut, K-3 gradeProj,
-- K-5 cutProjectable, K-6 kcutLossLoss / kcutLossMaxPlus / kcutLossHWM,
-- K-7 tests/reject/{UnprojectableChoice,InconsistentCut}.idr.
-- K-4 (only the two laws are used) is checked upstream by
-- scripts/minimal-laws.sh; it is NOT re-checked here.
--
-- Renaming: end/msg/choice -> End/Msg/Choice; local end/send/recv/select/
-- branch -> LEnd/Send/Recv/Select/Branch; grade↾ -> gradeAt; _↾_ ->
-- cutGlobal; _↾ₗ_ -> cutLocal; stop/cont-* -> Stop/Cont* (LStop/Cont* for
-- local cuts); sender/receiver/outside -> Sender/Receiver/Outside.
--
-- FRAGMENT (as upstream): finite global types with messages and binary
-- choice, plain merge, synchronous; no recursion, no full merge, no
-- delegation, no queues.
--
-- NO believe_me, NO postulate, NO assert_total.  %default total.

module TypedWasm.ABI.KCut

import Data.Nat
-- Re-exported so a consumer can REDUCE `role`, and with it any concrete
-- protocol's grades, at type level (role unfolds to decEq on Nat).
import public Decidable.Equality

import public TypedWasm.ABI.ResourceAlgebra
import TypedWasm.ABI.ResourceAlgebra.Loss
import TypedWasm.ABI.ResourceAlgebra.MaxPlus
import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

-- ============================================================================
-- Parties and roles — Party.agda
-- ============================================================================

||| A party, by number (decidable equality without primitives).
public export
Party : Type
Party = Nat

||| The role party p plays in an interaction s → r.
public export
data Role : (p, s, r : Party) -> Type where
  Sender   : p = s -> Role p s r
  Receiver : Not (p = s) -> p = r -> Role p s r
  Outside  : Not (p = s) -> Not (p = r) -> Role p s r

||| Classify p in the interaction s → r; sender takes precedence when s = r.
public export
role : (p, s, r : Party) -> Role p s r
role p s r with (decEq p s)
  role p s r | Yes e = Sender e
  role p s r | No ne with (decEq p r)
    role p s r | No ne | Yes e   = Receiver ne e
    role p s r | No ne | No ne'  = Outside ne ne'

-- ============================================================================
-- Graded global types and cuts — Global.agda
-- ============================================================================

||| A graded global protocol.
public export
data Global : Type -> Type where
  ||| Done.
  End    : Global g
  ||| s → r : x . continuation
  Msg    : (s, r : Party) -> g -> Global g -> Global g
  ||| s → r chooses between two continuations.
  Choice : (s, r : Party) -> g -> Global g -> Global g -> Global g

||| Global accumulation: sequence is ⊗, alternatives are ⊕.
public export
grade : ResourceAlgebra g => Global g -> g
grade End                 = oneG
grade (Msg _ _ x gl)      = otimes x (grade gl)
grade (Choice _ _ x l r)  = otimes x (oplus (grade l) (grade r))

||| The share of an interaction's grade that p experiences.
public export
at : ResourceAlgebra g => Role p s r -> g -> g
at (Sender _)     x = x
at (Receiver _ _) x = x
at (Outside _ _)  _ = oneG

||| Global accumulation restricted to p.  Agda `grade↾`.
public export
gradeAt : ResourceAlgebra g => Party -> Global g -> g
gradeAt p End                = oneG
gradeAt p (Msg s r x gl)     = otimes (at (role p s r) x) (gradeAt p gl)
gradeAt p (Choice s r x l k) = otimes (at (role p s r) x) (oplus (gradeAt p l) (gradeAt p k))

||| A frontier through a global protocol.
public export
data Cut : {g : Type} -> Global g -> Type where
  ||| Cut everything below here.
  Stop       : {gl : Global g} -> Cut gl
  ||| Keep the message and continue.
  ContMsg    : {s, r : Party} -> {x : g} -> {gl : Global g} ->
               Cut gl -> Cut (Msg s r x gl)
  ||| Keep the choice and continue into both branches.
  ContChoice : {s, r : Party} -> {x : g} -> {l, k : Global g} ->
               Cut l -> Cut k -> Cut (Choice s r x l k)

||| Truncate a protocol at a frontier.  Agda `_↾_`.
public export
cutGlobal : (gl : Global g) -> Cut gl -> Global g
cutGlobal _                  Stop             = End
cutGlobal (Msg s r x gl)     (ContMsg c)      = Msg s r x (cutGlobal gl c)
cutGlobal (Choice s r x l k) (ContChoice a b) = Choice s r x (cutGlobal l a) (cutGlobal k b)

-- ============================================================================
-- Graded local types and local cuts — Local.agda
-- ============================================================================

||| A graded endpoint type.
public export
data Local : Type -> Type where
  LEnd   : Local g
  Send   : Party -> g -> Local g -> Local g
  Recv   : Party -> g -> Local g -> Local g
  Select : Party -> g -> Local g -> Local g -> Local g
  Branch : Party -> g -> Local g -> Local g -> Local g

||| The endpoint's own timeline, graded.
public export
lgrade : ResourceAlgebra g => Local g -> g
lgrade LEnd               = oneG
lgrade (Send _ x l)       = otimes x (lgrade l)
lgrade (Recv _ x l)       = otimes x (lgrade l)
lgrade (Select _ x l k)   = otimes x (oplus (lgrade l) (lgrade k))
lgrade (Branch _ x l k)   = otimes x (oplus (lgrade l) (lgrade k))

||| A frontier through an endpoint type.
public export
data LCut : {g : Type} -> Local g -> Type where
  LStop      : {l : Local g} -> LCut l
  ContSend   : {q : Party} -> {x : g} -> {l : Local g} -> LCut l -> LCut (Send q x l)
  ContRecv   : {q : Party} -> {x : g} -> {l : Local g} -> LCut l -> LCut (Recv q x l)
  ContSelect : {q : Party} -> {x : g} -> {l, k : Local g} ->
               LCut l -> LCut k -> LCut (Select q x l k)
  ContBranch : {q : Party} -> {x : g} -> {l, k : Local g} ->
               LCut l -> LCut k -> LCut (Branch q x l k)

||| Truncate an endpoint at its frontier.  Agda `_↾ₗ_`.
public export
cutLocal : (l : Local g) -> LCut l -> Local g
cutLocal _                LStop            = LEnd
cutLocal (Send q x l)     (ContSend c)     = Send q x (cutLocal l c)
cutLocal (Recv q x l)     (ContRecv c)     = Recv q x (cutLocal l c)
cutLocal (Select q x l k) (ContSelect a b) = Select q x (cutLocal l a) (cutLocal k b)
cutLocal (Branch q x l k) (ContBranch a b) = Branch q x (cutLocal l a) (cutLocal k b)

-- ============================================================================
-- Projection — Projection.agda
-- ============================================================================

||| Prepend a send or receive for a participant; an outsider's continuation
||| is unchanged.
public export
projMsg : {s, r : Party} -> Role p s r -> g -> Local g -> Local g
projMsg {r} (Sender _)     x l = Send r x l
projMsg {s} (Receiver _ _) x l = Recv s x l
projMsg     (Outside _ _)  _ l = l

||| Form a selection or branch for a participant; an outsider takes the left
||| continuation as representative.
public export
projChoice : {s, r : Party} -> Role p s r -> g -> Local g -> Local g -> Local g
projChoice {r} (Sender _)     x l k = Select r x l k
projChoice {s} (Receiver _ _) x l k = Branch s x l k
projChoice     (Outside _ _)  _ l _ = l

||| p's endpoint.
public export
proj : Party -> Global g -> Local g
proj p End                = LEnd
proj p (Msg s r x gl)     = projMsg (role p s r) x (proj p gl)
proj p (Choice s r x l k) = projChoice (role p s r) x (proj p l) (proj p k)

||| What a choice demands of p: nothing if p takes part; plain merge (the two
||| branches project identically) if it does not.
public export
Merge : (p : Party) -> Role p s r -> Global g -> Global g -> Type
Merge p (Sender _)     _ _ = ()
Merge p (Receiver _ _) _ _ = ()
Merge p (Outside _ _)  l k = proj p l = proj p k

||| p's projection is well defined.
public export
data Projectable : (p : Party) -> Global g -> Type where
  PEnd    : Projectable p End
  PMsg    : {s, r : Party} -> {x : g} -> {gl : Global g} ->
            Projectable p gl -> Projectable p (Msg s r x gl)
  PChoice : {s, r : Party} -> {x : g} -> {l, k : Global g} ->
            Projectable p l -> Projectable p k -> Merge p (role p s r) l k ->
            Projectable p (Choice s r x l k)

||| Project a message cut.
public export
cutprojMsg : {s, r : Party} -> {x : g} -> {l : Local g} ->
             (rho : Role p s r) -> LCut l -> LCut (projMsg rho x l)
cutprojMsg (Sender _)     c = ContSend c
cutprojMsg (Receiver _ _) c = ContRecv c
cutprojMsg (Outside _ _)  c = c

||| Project a choice cut; an outsider keeps only the left cut.
public export
cutprojChoice : {s, r : Party} -> {x : g} -> {l, k : Local g} ->
                (rho : Role p s r) -> LCut l -> LCut k -> LCut (projChoice rho x l k)
cutprojChoice (Sender _)     a b = ContSelect a b
cutprojChoice (Receiver _ _) a b = ContBranch a b
cutprojChoice (Outside _ _)  a _ = a

||| Map a global frontier to p's endpoint.
public export
cutproj : {gl : Global g} -> (p : Party) -> Cut gl -> LCut (proj p gl)
cutproj                          p Stop             = LStop
cutproj {gl = Msg s r x gl'}     p (ContMsg c)      = cutprojMsg (role p s r) (cutproj p c)
cutproj {gl = Choice s r x l k}  p (ContChoice a b) =
  cutprojChoice (role p s r) (cutproj p a) (cutproj p b)

||| A cut is consistent for p when plain merge still holds on the truncated
||| branches of every choice p does not take part in.
public export
data Consistent : (p : Party) -> {gl : Global g} -> Cut gl -> Type where
  CStop   : {gl : Global g} -> Consistent p (Stop {gl})
  CMsg    : {s, r : Party} -> {x : g} -> {gl : Global g} -> {c : Cut gl} ->
            Consistent p c -> Consistent p (ContMsg {s} {r} {x} c)
  CChoice : {s, r : Party} -> {x : g} -> {l, k : Global g} ->
            {a : Cut l} -> {b : Cut k} ->
            Consistent p a -> Consistent p b ->
            Merge p (role p s r) (cutGlobal l a) (cutGlobal k b) ->
            Consistent p (ContChoice {s} {r} {x} a b)

-- ============================================================================
-- K-CUT-LOSS — KCut.agda
-- ============================================================================

-- (A) Projection commutes with cutting (K-2).

projCutMsg : {s, r : Party} -> (rho : Role p s r) -> (x : g) -> (l : Local g) -> (c : LCut l) ->
             projMsg rho x (cutLocal l c) = cutLocal (projMsg rho x l) (cutprojMsg {x} rho c)
projCutMsg (Sender _)     _ _ _ = Refl
projCutMsg (Receiver _ _) _ _ _ = Refl
projCutMsg (Outside _ _)  _ _ _ = Refl

projCutChoice : {s, r : Party} -> (rho : Role p s r) -> (x : g) -> (l, k : Local g) ->
                (a : LCut l) -> (b : LCut k) ->
                projChoice rho x (cutLocal l a) (cutLocal k b)
              = cutLocal (projChoice rho x l k) (cutprojChoice {x} rho a b)
projCutChoice (Sender _)     _ _ _ _ _ = Refl
projCutChoice (Receiver _ _) _ _ _ _ _ = Refl
projCutChoice (Outside _ _)  _ _ _ _ _ = Refl

||| Agda `proj-cut` (K-2): no side-conditions, no algebra laws.
public export
projCut : (p : Party) -> (gl : Global g) -> (c : Cut gl) ->
          proj p (cutGlobal gl c) = cutLocal (proj p gl) (cutproj p c)
projCut p _                  Stop             = Refl
projCut p (Msg s r x gl)     (ContMsg c)      =
  trans (cong (projMsg (role p s r) x) (projCut p gl c))
        (projCutMsg (role p s r) x (proj p gl) (cutproj p c))
projCut p (Choice s r x l k) (ContChoice a b) =
  trans (cong2 (projChoice (role p s r) x) (projCut p l a) (projCut p k b))
        (projCutChoice (role p s r) x (proj p l) (proj p k) (cutproj p a) (cutproj p b))

-- (B) The restricted global grade is the grade of the projection (K-3).

gradeProjMsg : ResourceAlgebra g => {s, r : Party} ->
               (rho : Role p s r) -> (x : g) -> {y : g} -> {l : Local g} ->
               y = lgrade l -> otimes (at rho x) y = lgrade (projMsg rho x l)
gradeProjMsg (Sender _)         x e = cong (otimes x) e
gradeProjMsg (Receiver _ _)     x e = cong (otimes x) e
gradeProjMsg (Outside _ _) {y}  _ e = trans (seqUnitL y) e

gradeProjChoice : ResourceAlgebra g => {p, s, r : Party} ->
                  (rho : Role p s r) -> (x : g) -> {y1, y2 : g} -> {l, k : Global g} ->
                  y1 = lgrade (proj p l) -> y2 = lgrade (proj p k) ->
                  Merge p rho l k ->
                  otimes (at rho x) (oplus y1 y2) = lgrade (projChoice rho x (proj p l) (proj p k))
gradeProjChoice (Sender _)     x e1 e2 _ = cong (otimes x) (cong2 oplus e1 e2)
gradeProjChoice (Receiver _ _) x e1 e2 _ = cong (otimes x) (cong2 oplus e1 e2)
gradeProjChoice {p} (Outside _ _) _ {y1} {y2} {l} e1 e2 m =
  trans (seqUnitL (oplus y1 y2))
  (trans (cong2 oplus e1 e2)
  (trans (cong (oplus (lgrade (proj p l))) (cong lgrade (sym m)))
         (altIdem (lgrade (proj p l)))))

||| Agda `grade-proj` (K-3).
public export
gradeProj : ResourceAlgebra g => (p : Party) -> (gl : Global g) -> Projectable p gl ->
            gradeAt p gl = lgrade (proj p gl)
gradeProj p End                PEnd               = Refl
gradeProj p (Msg s r x gl)     (PMsg pr)          =
  gradeProjMsg (role p s r) x (gradeProj p gl pr)
gradeProj p (Choice s r x l k) (PChoice pl pk m)  =
  gradeProjChoice (role p s r) x (gradeProj p l pl) (gradeProj p k pk) m

-- (C) A consistent cut yields a projectable protocol (K-5).

||| Agda `cut-projectable` (K-5).
public export
cutProjectable : (p : Party) -> (gl : Global g) -> (c : Cut gl) -> Consistent p c ->
                 Projectable p (cutGlobal gl c)
cutProjectable p _                  Stop             CStop             = PEnd
cutProjectable p (Msg s r x gl)     (ContMsg c)      (CMsg kc)         =
  PMsg (cutProjectable p gl c kc)
cutProjectable p (Choice s r x l k) (ContChoice a b) (CChoice ka kb m) =
  PChoice (cutProjectable p l a ka) (cutProjectable p k b kb) m

||| K-CUT-LOSS (K-1).  Agda `kcut-loss`.
public export
kcutLoss : ResourceAlgebra g => (p : Party) -> (gl : Global g) -> (c : Cut gl) ->
           Consistent p c ->
           gradeAt p (cutGlobal gl c) = lgrade (cutLocal (proj p gl) (cutproj p c))
kcutLoss p gl c k =
  trans (gradeProj p (cutGlobal gl c) (cutProjectable p gl c k))
        (cong lgrade (projCut p gl c))

||| The uncut special case.  Agda `kcut-loss-full`.
public export
kcutLossFull : ResourceAlgebra g => (p : Party) -> (gl : Global g) -> Projectable p gl ->
               gradeAt p gl = lgrade (proj p gl)
kcutLossFull = gradeProj

-- ============================================================================
-- K-6  Discharged at the three kernel instances — Instances.agda
-- ============================================================================

||| K-CUT-LOSS for echo loss (min-plus).
public export
kcutLossLoss : (p : Party) -> (gl : Global LossGrade) -> (c : Cut gl) -> Consistent p c ->
               gradeAt p (cutGlobal gl c) = lgrade (cutLocal (proj p gl) (cutproj p c))
kcutLossLoss = kcutLoss

||| K-CUT-LOSS for worst-case cost (max-plus).
public export
kcutLossMaxPlus : (p : Party) -> (gl : Global MaxPlusGrade) -> (c : Cut gl) -> Consistent p c ->
                  gradeAt p (cutGlobal gl c) = lgrade (cutLocal (proj p gl) (cutproj p c))
kcutLossMaxPlus = kcutLoss

||| K-CUT-LOSS for occupancy (high-water mark).
public export
kcutLossHWM : (p : Party) -> (gl : Global HWMGrade) -> (c : Cut gl) -> Consistent p c ->
              gradeAt p (cutGlobal gl c) = lgrade (cutLocal (proj p gl) (cutproj p c))
kcutLossHWM = kcutLoss

-- ============================================================================
-- A worked protocol — Instances.agda `Worked` (computed readings: TESTED)
-- ============================================================================
--
-- Parties 0 (client), 1 (broker), 2 (server):
--   0 → 1 : a . 1 → 2 : b . 0 → 2 chooses { 2 → 1 : c . end | 2 → 1 : c . end }
-- The broker is outside the choice and both branches project identically
-- for it, so its projection is plain-mergeable.

||| The worked protocol.
public export
worked : ResourceAlgebra g => (a, b, c : g) -> Global g
worked a b c = Msg 0 1 a (Msg 1 2 b (Choice 0 2 oneG (Msg 2 1 c End) (Msg 2 1 c End)))

||| Cut after the broker has forwarded, before the server answers.
public export
workedCut : ResourceAlgebra g => {a, b, c : g} -> Cut (worked a b c)
workedCut = ContMsg (ContMsg (ContChoice Stop Stop))

||| The broker's projection is well defined.
public export
workedProjectable : ResourceAlgebra g => {a, b, c : g} -> Projectable 1 (worked a b c)
workedProjectable = PMsg (PMsg (PChoice (PMsg PEnd) (PMsg PEnd) Refl))

||| The cut is consistent for the broker.
public export
workedConsistent : ResourceAlgebra g => {a, b, c : g} -> Consistent 1 (workedCut {a} {b} {c})
workedConsistent = CMsg (CMsg (CChoice CStop CStop Refl))

||| The keystone at that cut, for the broker, in any algebra.
public export
brokerCut : ResourceAlgebra g => (a, b, c : g) ->
            gradeAt 1 (cutGlobal (worked a b c) (workedCut {a} {b} {c}))
          = lgrade (cutLocal (proj 1 (worked a b c)) (cutproj 1 (workedCut {a} {b} {c})))
brokerCut a b c = kcutLoss 1 (worked a b c) workedCut workedConsistent

||| Loss: the broker's restricted grade over the whole protocol is 1 + 2 + 5.
public export
lossBroker : gradeAt 1 (worked (Finite 1) (Finite 2) (Finite 5)) = Finite 8
lossBroker = Refl

||| Loss: at the cut only a and b remain.
public export
lossBrokerCut : gradeAt 1 (cutGlobal (worked (Finite 1) (Finite 2) (Finite 5)) KCut.workedCut)
              = Finite 3
lossBrokerCut = Refl

||| MaxPlus: the same protocol costs 8.
public export
maxPlusBroker : gradeAt 1 (worked (Val 1) (Val 2) (Val 5)) = Val 8
maxPlusBroker = Refl

||| HWM: peaks 1, 2 and 5 with nothing held between them reach 5, not 8.
public export
hwmBroker : peak (gradeAt 1 (worked (MkHWM 1 0 LTEZero) (MkHWM 2 0 LTEZero) (MkHWM 5 0 LTEZero))) = 5
hwmBroker = Refl

||| HWM: at the cut the peak is 2.
public export
hwmBrokerCut : peak (gradeAt 1 (cutGlobal (worked (MkHWM 1 0 LTEZero) (MkHWM 2 0 LTEZero) (MkHWM 5 0 LTEZero))
                                          KCut.workedCut)) = 2
hwmBrokerCut = Refl
