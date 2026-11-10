-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Certificates about one access.
--
-- `LevelAttestationW n` (Proofs.idr) carries a witness for level n, but the
-- thing each witness is about is hidden in an implicit argument.  A
-- `ProgressiveW n` chain can therefore be assembled from witnesses about
-- unrelated things, and some levels are inhabited for any program:
--
--   AttestL1W []                      -- any schema
--   AttestL3W (TypeCompat {ty = U8})  -- reflexivity, U8 against U8
--   AttestL5W zeroInBounds            -- index 0 of some non-empty region
--   AttestL6W (MkAccessResult v)      -- any value of any type
--
-- So `witnessAchievedEntails` returns a witness for *some* object, not for
-- the access the certificate was meant to describe.
--
-- `Subject` names that access: the schema it reads, the field, the type it
-- reads at, the pointer's kind and lifetime, the index and instance count,
-- and the function- and program-level facts levels 8 to 15 talk about.
-- `Attest subj n` is a level-n witness *about subj*, and `Certified subj n`
-- is a chain of them.  Every level of one certificate therefore speaks about
-- the same access:
--
--   * L2 binds the field to the schema and fixes its declared type
--     (`subjFieldTy`), and L3 relates that type to the access type
--     (`subjAccessTy`).  Reading an I32 field at F64 has no L3 witness
--     (tests/reject/AccessAtWrongType.idr).
--   * L4 and L7 are indexed by the subject's schema: a pointer whose schema
--     differs does not fit (tests/reject/ForeignPointer.idr). The index is
--     the schema, not the region, so two regions with the same schema are
--     not told apart.
--   * L5 is about the subject's index and count (tests/reject/
--     CertifiedOutOfBounds.idr), and L6 returns the subject's access type.
--
-- `forget` and `forgetChain` drop the subject and give back the
-- `LevelAttestationW` / `ProgressiveW` forms, so this is a strengthening of
-- those, not a different object.
--
-- What this does not change: each level's witness is as strong as its type
-- in the module that defines it.  `ExclusiveWitness` (L7) is a scope name,
-- `CompletedProtocol` (L10) any `FreeResult`, and `Level12Proof` (L12) and
-- `IsolatedModule` (L13) are not indexed by anything a `Subject` can name.
-- Indexing ties the levels to one access; it does not make a weak level
-- stronger.  L1 has no predicate of its own (parse-time validity); its
-- attestation is the subject's schema.
--
-- What this does not prove: that the subject describes the program.  A
-- certificate is about its `Subject`; that `subjSchema` is the region's
-- schema and `subjCount` its instance count is the claim of whoever builds
-- the subject (the producer, or the verifier reading its carrier sections),
-- not something this module checks.
--
-- No `believe_me`, `assert_total` or `postulate`; `%default total`.
module TypedWasm.ABI.Certified

import Data.Nat
import TypedWasm.ABI.Region
import TypedWasm.ABI.TypedAccess
import TypedWasm.ABI.Levels
import TypedWasm.ABI.Pointer
import TypedWasm.ABI.Effects
import TypedWasm.ABI.Lifetime
import TypedWasm.ABI.Linear
import TypedWasm.ABI.MultiModule
import TypedWasm.ABI.Tropical
import TypedWasm.ABI.Epistemic
import TypedWasm.ABI.ModuleIsolation
import TypedWasm.ABI.SessionProtocol
import TypedWasm.ABI.ResourceCapabilities
import TypedWasm.ABI.Proofs

%default total

-- ============================================================================
-- The subject of a certificate
-- ============================================================================

||| The access a certificate is about, and the function and program around
||| it.  Levels 1-7 talk about the access, 8-10 about the enclosing function,
||| 11-15 about the program.
public export
record Subject where
  constructor MkSubject
  ||| The region schema the access reads (L1, L2, L4, L7).
  subjSchema    : Schema
  ||| The field the access names (L2).
  subjField     : String
  ||| The field's declared type in `subjSchema` (fixed by L2).
  subjFieldTy   : WasmType
  ||| The type the access reads or writes at (L3, L6).
  subjAccessTy  : WasmType
  ||| The pointer's kind and lifetime (L4).
  subjPtrKind   : PtrKind
  subjPtrLife   : Levels.Lifetime
  ||| The instance index and the region's instance count (L5).
  subjIndex     : Nat
  subjCount     : Nat
  ||| Declared and actual effects of the enclosing function (L8).
  subjDeclared  : EffectSet
  subjActual    : EffectSet
  ||| The reference's lifetime and the scope it is used in (L9).
  subjRefLife   : Lifetime.Lifetime
  subjScopeLife : Lifetime.Lifetime
  ||| The allocation token the function must free (L10).
  subjToken     : Nat
  ||| The size of the cost matrix (L11).
  subjCostN     : Nat
  ||| The session protocol (L14).
  subjProtocol  : Protocol
  ||| The module whose capabilities the function draws on (L15).
  subjCaps      : ModuleCaps

-- ============================================================================
-- Attestations about a subject
-- ============================================================================

||| A level-`n` witness about the subject `s`.
public export
data Attest : (s : Subject) -> (n : Nat) -> Type where
  ||| L1: the subject's schema is the instruction's schema.
  AttS1  : Attest s 1
  ||| L2: the field is in the schema, and its declared type is `subjFieldTy`.
  AttS2  : (fi : FieldIn (subjField s) (subjSchema s))
        -> fieldType (lookupField fi) = subjFieldTy s
        -> Attest s 2
  ||| L3: the access type is compatible with the field's declared type.
  AttS3  : WasmTypeCompat (subjFieldTy s) (subjAccessTy s) -> Attest s 3
  ||| L4: a non-null pointer into the subject's schema.
  AttS4  : Pointer.Ptr (subjPtrKind s) (subjSchema s) (subjPtrLife s) NonNull
        -> Attest s 4
  ||| L5: the index is in bounds of the instance count.
  AttS5  : InBounds (subjIndex s) (subjCount s) -> Attest s 5
  ||| L6: the access returns a value of the access type.
  AttS6  : AccessResult (subjAccessTy s) -> Attest s 6
  ||| L7: no other pointer to the subject's schema is live.
  AttS7  : ExclusiveWitness (subjSchema s) -> Attest s 7
  ||| L8: the function's actual effects are among its declared ones.
  AttS8  : EffectSubsumes (subjDeclared s) (subjActual s) -> Attest s 8
  ||| L9: the reference outlives the scope it is used in.
  AttS9  : Lifetime.Outlives (subjRefLife s) (subjScopeLife s) -> Attest s 9
  ||| L10: the function's allocation token is freed.
  AttS10 : CompletedProtocol (subjToken s) -> Attest s 10
  ||| L11: every access route is cost-bounded.
  AttS11 : AllPairsCosts (subjCostN s) -> Attest s 11
  ||| L12: epistemic freshness (not indexed by the subject; see header).
  AttS12 : Level12Proof -> Attest s 12
  ||| L13: module isolation (not indexed by the subject; see header).
  AttS13 : IsolatedModule -> Attest s 13
  ||| L14: the subject's protocol is well formed.
  AttS14 : WellFormedProtocol (subjProtocol s) -> Attest s 14
  ||| L15: the function's capabilities are contained in its module's.
  AttS15 : FunctionCaps (subjCaps s) -> Attest s 15

||| Drop the subject: the witness-carrying attestation of `Proofs.idr`.
public export
forget : {s : Subject} -> Attest s n -> LevelAttestationW n
forget {s} AttS1          = AttestL1W (subjSchema s)
forget (AttS2 fi _)       = AttestL2W fi
forget (AttS3 w)          = AttestL3W w
forget (AttS4 w)          = AttestL4W w
forget (AttS5 w)          = AttestL5W w
forget (AttS6 w)          = AttestL6W w
forget (AttS7 w)          = AttestL7W w
forget (AttS8 w)          = AttestL8W w
forget (AttS9 w)          = AttestL9W w
forget (AttS10 w)         = AttestL10W w
forget (AttS11 w)         = AttestL11W w
forget (AttS12 w)         = AttestL12W w
forget (AttS13 w)         = AttestL13W w
forget (AttS14 w)         = AttestL14W w
forget (AttS15 w)         = AttestL15W w

-- ============================================================================
-- Certificates: a chain of attestations about one subject
-- ============================================================================

||| A witness about `s` for every level from 1 up to `n`, in order.
public export
data Certified : (s : Subject) -> (n : Nat) -> Type where
  StartS   : Attest s 1 -> Certified s 1
  AdvanceS : {n : Nat} -> Certified s n -> Attest s (S n) -> Certified s (S n)

||| Drop the subject from every link: the `ProgressiveW` chain.
public export
forgetChain : {s : Subject} -> Certified s n -> ProgressiveW n
forgetChain (StartS a)     = StartW (forget a)
forgetChain (AdvanceS c a) = AdvanceW (forgetChain c) (forget a)

||| The witness about `s` for the chain's top level.
public export
certTop : Certified s n -> Attest s n
certTop (StartS a)     = a
certTop (AdvanceS _ a) = a

||| Level monotonicity about one subject: a certificate that reaches `n`
||| holds a witness about the same `s` for every level `m`, `1 <= m <= n`.
public export
certMonotone : Certified s n
            -> (m : Nat)
            -> LTE 1 m
            -> LTE m n
            -> Attest s m
certMonotone (StartS _) Z         one _            = absurd one
certMonotone (StartS a) (S Z)     _   _            = a
certMonotone (StartS _) (S (S _)) _   (LTESucc le) = absurd le
certMonotone (AdvanceS prev a) m  one le =
  case lteSuccSplit le of
    Left le' => certMonotone prev m one le'
    Right eq => rewrite eq in a

||| Monotonicity commutes with forgetting the subject: the witness the
||| subject-free chain gives for level `m` is the one this chain gives,
||| forgotten.
public export
certMonotoneForget : {s : Subject}
                  -> (c : Certified s n)
                  -> (m : Nat)
                  -> (one : LTE 1 m)
                  -> (le : LTE m n)
                  -> levelMonotoneW (forgetChain c) m one le
                   = forget (certMonotone c m one le)
certMonotoneForget (StartS _) Z         one _            = absurd one
certMonotoneForget (StartS a) (S Z)     _   _            = Refl
certMonotoneForget (StartS _) (S (S _)) _   (LTESucc le) = absurd le
certMonotoneForget (AdvanceS prev a) m  one le with (lteSuccSplit le)
  _ | Left le' = certMonotoneForget prev m one le'
  _ | Right eq = rewrite eq in Refl

-- ============================================================================
-- What a certificate says about its access
-- ============================================================================

||| `FieldTyped name ty schema`: the schema has a field called `name`
||| whose declared type is `ty`.
public export
data FieldTyped : (name : String) -> (ty : WasmType) -> (schema : Schema) -> Type where
  MkFieldTyped : (fi : FieldIn name schema)
              -> fieldType (lookupField fi) = ty
              -> FieldTyped name ty schema

||| Compatible wasm types are equal (`WasmTypeCompat` has one constructor).
public export
compatEq : WasmTypeCompat a b -> a = b
compatEq TypeCompat = Refl

||| A certificate at level 3 or above says the access reads a field of its
||| schema at that field's declared type.  This is the statement the
||| subject-free chain cannot make: there, L2's field and L3's types are
||| about unrelated things.
public export
certFieldTyped : {s : Subject}
              -> Certified s n
              -> LTE 3 n
              -> FieldTyped (subjField s) (subjAccessTy s) (subjSchema s)
certFieldTyped c le =
  case (certMonotone c 2 (LTESucc LTEZero) (lteSuccLeft le), certMonotone c 3 (LTESucc LTEZero) le) of
    (AttS2 fi eq, AttS3 w) => MkFieldTyped fi (trans eq (compatEq w))

||| A certificate at level 4 or above holds a non-null pointer into the
||| access's own schema.
public export
certPointer : Certified s n
           -> LTE 4 n
           -> Pointer.Ptr (subjPtrKind s) (subjSchema s) (subjPtrLife s) NonNull
certPointer c le with (certMonotone c 4 (LTESucc LTEZero) le)
  _ | AttS4 p = p

||| A certificate at level 5 or above says the access's index is in bounds.
public export
certInBounds : Certified s n -> LTE 5 n -> InBounds (subjIndex s) (subjCount s)
certInBounds c le with (certMonotone c 5 (LTESucc LTEZero) le)
  _ | AttS5 b = b

||| A certificate at level 6 or above returns a value of the access type.
public export
certResult : Certified s n -> LTE 6 n -> AccessResult (subjAccessTy s)
certResult c le with (certMonotone c 6 (LTESucc LTEZero) le)
  _ | AttS6 r = r

-- ============================================================================
-- The simple-read certificate about one access
-- ============================================================================

||| `simpleReadChain` (Proofs.idr) with every witness about the same access.
public export
simpleReadCertified : {s : Subject}
                   -> (fi : FieldIn (subjField s) (subjSchema s))
                   -> (fieldTy : fieldType (lookupField fi) = subjFieldTy s)
                   -> (compat : WasmTypeCompat (subjFieldTy s) (subjAccessTy s))
                   -> (ptr : Pointer.Ptr (subjPtrKind s) (subjSchema s) (subjPtrLife s) NonNull)
                   -> (bounds : InBounds (subjIndex s) (subjCount s))
                   -> (result : AccessResult (subjAccessTy s))
                   -> Certified s 6
simpleReadCertified fi fieldTy compat ptr bounds result =
  AdvanceS (AdvanceS (AdvanceS (AdvanceS (AdvanceS
    (StartS AttS1)
    (AttS2 fi fieldTy)) (AttS3 compat)) (AttS4 ptr)) (AttS5 bounds)) (AttS6 result)

||| Forgetting the subject of `simpleReadCertified` gives `simpleReadChain`
||| on the same witnesses, so its legacy projection is `simpleReadCert`.
||| Stated for a subject whose field type and access type are one `ty`:
||| `WasmTypeCompat` admits no other case, and `simpleReadChain` asks for
||| `WasmTypeCompat ty ty`.
public export
simpleReadCertifiedForget :
     {sch : Schema} -> {f : String} -> {ty : WasmType}
  -> {k : PtrKind} -> {pl : Levels.Lifetime}
  -> {i, cnt : Nat}
  -> {d, a : EffectSet} -> {rl, sl : Lifetime.Lifetime}
  -> {tok, cn : Nat} -> {p : Protocol} -> {caps : ModuleCaps}
  -> (fi : FieldIn f sch)
  -> (fieldTy : fieldType (lookupField fi) = ty)
  -> (compat : WasmTypeCompat ty ty)
  -> (ptr : Pointer.Ptr k sch pl NonNull)
  -> (bounds : InBounds i cnt)
  -> (result : AccessResult ty)
  -> forgetChain (simpleReadCertified
                    {s = MkSubject sch f ty ty k pl i cnt d a rl sl tok cn p caps}
                    fi fieldTy compat ptr bounds result)
   = simpleReadChain sch fi compat ptr bounds result
simpleReadCertifiedForget _ _ _ _ _ _ = Refl

-- ============================================================================
-- A concrete certificate
-- ============================================================================
--
-- The type is inhabited: instance 0 of a one-instance region with an I32
-- field "x", read at I32.  `exampleFieldTyped` reads the typing fact back
-- out of the certificate.

||| The access: field "x" (I32) of a one-instance region, read at I32.
public export
exampleSubject : Subject
exampleSubject =
  MkSubject [MkField "x" I32] "x" I32 I32 Owning Levels.Static 0 1
            [] [] Lifetime.Static Lifetime.Static 0 0
            (MkProtocol (MkSessionId "example") [] [] Nothing) emptyModuleCaps

||| A level-6 certificate about `exampleSubject`.
public export
exampleCertified : Certified Certified.exampleSubject 6
exampleCertified =
  simpleReadCertified FieldHere Refl TypeCompat (MkPtr 64) zeroInBounds
                      (MkAccessResult 7)

||| What the certificate says about its access.
public export
exampleFieldTyped : FieldTyped "x" I32 [MkField "x" I32]
exampleFieldTyped = certFieldTyped exampleCertified (LTESucc (LTESucc (LTESucc LTEZero)))
