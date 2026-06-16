-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- src/abi/TypedWasm/ABI/AccessTypingSpec.idr
--
-- T5a (verifier↔spec link) for the Tier-2 access-TYPING obligation.
--
-- This is the spec-of-record for what the Rust
-- `verify_access_typing_from_module` pass (typed-wasm-verify) establishes
-- when it returns a clean `AccessTypingReport` (errors = []). It mirrors
-- `VerifierSpec.idr`'s TrustedFixture design, but for per-site access
-- typing rather than L7/L10 ownership, and it is grounded in
-- `PackedLayout.idr` (T4): field widths come from `packedScalarSize`, so
-- the spec's offset/extent arithmetic IS the layout the producer emits.
--
-- The determine-vs-bound asymmetry made explicit:
--
--   * `SiteWellTyped` (the spec predicate) is the DETERMINABLE side — it
--     is fixed entirely by the schema and the emitted op (type, width,
--     offset, in-region), exactly what `mem_op_matches_field` +
--     `field_byte_offset` + the region-bounds check decide in Rust. The
--     equality holds by construction.
--   * `TypedAccessFixture` (the trust-injection) is the BOUNDABLE side —
--     constructing one ASSUMES the Rust pass faithfully decoded the
--     module's operator stream (the decode-faithfulness hypothesis; the
--     `SoundWarrant` / ADR-0005 analogue). The Idris spec cannot see the
--     wasm bytes, so this is named here as a trust-injection, not proven.
--     Grep `MkTypedAccessFixture` to enumerate every such injection.
--
-- The agreement lemmas below are TOTAL by case analysis: the trust budget
-- lives entirely inside any `TypedAccessFixture` the input carried, spent
-- at the site that constructed it.
--
-- NO `believe_me`, NO `assert_total`, NO `postulate`, NO `sorry`,
-- NO `assert_smaller`. `%default total`.

module TypedWasm.ABI.AccessTypingSpec

import TypedWasm.ABI.Region
import TypedWasm.ABI.PackedLayout
import Data.Nat
import Data.List
import Data.List.Quantifiers
import Decidable.Equality

%default total

-- ============================================================================
-- Field classification (width + int/float + signedness)
-- ============================================================================

||| The storage class of a scalar field: an integer of a given byte width
||| and signedness, or a float of a given byte width. `WBool` classifies
||| as a 1-byte unsigned integer (packed-region storage; see PackedLayout).
public export
data FieldClass : Type where
  IntF   : (bytes : Nat) -> (signed : Bool) -> FieldClass
  FloatF : (bytes : Nat) -> FieldClass

public export
fieldClass : WasmType -> FieldClass
fieldClass U8    = IntF 1 False
fieldClass U16   = IntF 2 False
fieldClass U32   = IntF 4 False
fieldClass U64   = IntF 8 False
fieldClass I8    = IntF 1 True
fieldClass I16   = IntF 2 True
fieldClass I32   = IntF 4 True
fieldClass I64   = IntF 8 True
fieldClass F32   = FloatF 4
fieldClass F64   = FloatF 8
fieldClass WBool = IntF 1 False

-- ============================================================================
-- Spec-level memory ops (mirrors typed-wasm-verify `MemOp`)
-- ============================================================================

||| The classification of the memory op the verifier decodes at a pinned
||| site. Loads carry signedness (wasm `load8_s` vs `load8_u`); stores
||| collapse it (only `store8` / `store16` exist) — exactly the asymmetry
||| in the Rust `mem_op_matches_field`.
public export
data OpClass : Type where
  IntLoad    : (bytes : Nat) -> (signed : Bool) -> OpClass
  IntStore   : (bytes : Nat) -> OpClass
  FloatLoad  : (bytes : Nat) -> OpClass
  FloatStore : (bytes : Nat) -> OpClass

||| Does the decoded op legitimately load OR store a field of type `ty`?
||| A load must match width AND signedness; a store must match width only
||| (sign-agnostic). Floats match width. Transliteration of the Rust
||| `mem_op_matches_field`.
public export
opMatchesField : OpClass -> WasmType -> Bool
opMatchesField (IntLoad b s) ty =
  case fieldClass ty of
    IntF b' s' => b == b' && s == s'
    FloatF _   => False
opMatchesField (IntStore b) ty =
  case fieldClass ty of
    IntF b' _ => b == b'
    FloatF _  => False
opMatchesField (FloatLoad b) ty =
  case fieldClass ty of
    FloatF b' => b == b'
    IntF _ _  => False
opMatchesField (FloatStore b) ty =
  case fieldClass ty of
    FloatF b' => b == b'
    IntF _ _  => False

-- ============================================================================
-- Spec access site
-- ============================================================================

||| A pinned access site, projected to the facts the typing check decides.
||| `siteFieldOff` is the field's PACKED byte offset (computed by
||| `PackedLayout.packedOffsetsFrom` on the Rust side, = `resolve_field`);
||| `siteRegionSz` is the region's `packedSize`. Bundling these projected
||| facts keeps the predicate independent of how the schema was walked.
public export
record SpecSite where
  constructor MkSpecSite
  siteOp       : OpClass     -- the op decoded at the pinned instruction index
  siteOffset   : Nat         -- the op's static memarg offset
  siteField    : WasmType    -- the declared type of the field it reaches
  siteFieldOff : Nat         -- the field's packed byte offset (PackedLayout)
  siteRegionSz : Nat         -- the region's packed byte size (PackedLayout)

-- ============================================================================
-- The spec predicate: a site is well-typed
-- ============================================================================

||| `SiteWellTyped s` holds when, exactly as the Rust pass decides:
|||   (1) the decoded op is a load/store of the field's type & width,
|||   (2) its static offset equals the field's packed byte offset, and
|||   (3) the field's extent `[off, off + width)` stays within the region.
||| The width is `packedScalarSize (siteField s)` — the SAME size T4's
||| PackedLayout assigns — so this predicate is grounded in the canonical
||| packed layout, not a fresh notion.
public export
data SiteWellTyped : SpecSite -> Type where
  MkSiteWellTyped :
       (opMatchesField (siteOp s) (siteField s) = True)
    -> (siteOffset s = siteFieldOff s)
    -> LTE (siteFieldOff s + packedScalarSize (siteField s)) (siteRegionSz s)
    -> SiteWellTyped s

||| The spec-of-record acceptance criterion for the access-typing pass:
||| EVERY pinned site is well-typed (the Rust `errors = []` condition).
public export
AccessTypingClean : List SpecSite -> Type
AccessTypingClean = All SiteWellTyped

-- A pinned site that is well-typed really does carry the op/field match
-- (a projection showing the predicate has content, not just shape).
export
wellTypedMatches : SiteWellTyped s -> opMatchesField (siteOp s) (siteField s) = True
wellTypedMatches (MkSiteWellTyped m _ _) = m

-- ...and its offset really equals the packed field offset.
export
wellTypedOffsetExact : SiteWellTyped s -> siteOffset s = siteFieldOff s
wellTypedOffsetExact (MkSiteWellTyped _ o _) = o

-- ============================================================================
-- Trusted fixture — the access-typing trust-injection (the BOUND)
-- ============================================================================

||| Packages a clean verdict from the Rust `verify_access_typing_from_module`
||| pass: a name/id plus the structural witness that every site is
||| well-typed. CONSTRUCTING this is the trust-injection moment — it
||| assumes the Rust pass decoded the operator stream faithfully (the
||| decode-faithfulness hypothesis; the determine-vs-bound BOUND). Grep
||| `MkTypedAccessFixture` to enumerate access-typing trust injections.
public export
record TypedAccessFixture (sites : List SpecSite) where
  constructor MkTypedAccessFixture
  tafName    : String
  tafId      : Nat
  tafWitness : AccessTypingClean sites

-- ============================================================================
-- Spec / verifier acceptance (mirrors VerifierSpec)
-- ============================================================================

||| The spec's access-typing acceptance: exactly the structural witness.
public export
data TypedSpecAccepts : List SpecSite -> Type where
  MkTypedSpecAccepts : AccessTypingClean sites -> TypedSpecAccepts sites

||| Verifier acceptance for access typing.
|||   * `TVAStructural` — acceptance from the same structural predicate the
|||     spec uses; no external trust.
|||   * `TVADifferential` — acceptance attested by the Rust pass via a
|||     `TypedAccessFixture`; the trust-injection is its construction.
public export
data TypedVerifierAccepts : List SpecSite -> Type where
  TVAStructural   : AccessTypingClean sites -> TypedVerifierAccepts sites
  TVADifferential : TypedAccessFixture sites -> TypedVerifierAccepts sites

||| Smart constructor: verifier acceptance from a clean Rust verdict.
public export
typedAccessAttested :
     (name : String) -> (fid : Nat)
  -> AccessTypingClean sites
  -> TypedVerifierAccepts sites
typedAccessAttested name fid w = TVADifferential (MkTypedAccessFixture name fid w)

||| Project a fixture into the spec via its wrapped witness.
public export
typedTrustedToSpec : TypedAccessFixture sites -> TypedSpecAccepts sites
typedTrustedToSpec (MkTypedAccessFixture _ _ w) = MkTypedSpecAccepts w

-- ============================================================================
-- The agreement lemmas (total by case analysis)
-- ============================================================================

||| Soundness: if the Rust access-typing pass accepts a site list, the
||| Idris spec accepts it too. Total. The differential case surfaces the
||| structural witness the Rust pass attested.
export
typedVerifierIsSound :
     (sites : List SpecSite)
  -> TypedVerifierAccepts sites
  -> TypedSpecAccepts sites
typedVerifierIsSound _ (TVAStructural w) = MkTypedSpecAccepts w
typedVerifierIsSound _ (TVADifferential (MkTypedAccessFixture _ _ w)) =
  MkTypedSpecAccepts w

||| Completeness: if the spec accepts, the verifier accepts (structurally,
||| no trust required). Total.
export
typedVerifierIsComplete :
     (sites : List SpecSite)
  -> TypedSpecAccepts sites
  -> TypedVerifierAccepts sites
typedVerifierIsComplete _ (MkTypedSpecAccepts w) = TVAStructural w

||| Spec acceptance really delivers the per-site witnesses (content, not
||| just shape): the cleanness predicate is the full `All` witness.
export
specAcceptsWitness : TypedSpecAccepts sites -> AccessTypingClean sites
specAcceptsWitness (MkTypedSpecAccepts w) = w

-- ============================================================================
-- T5-proper kernel: the spec acceptance criterion is an EXECUTABLE checker
-- ============================================================================
--
-- `SiteWellTyped` is decidable (each of its three conjuncts is: a Bool
-- equality, a Nat equality, and an LTE), so `AccessTypingClean` is too.
-- The spec's acceptance predicate is therefore not merely "holds by
-- construction" — it is COMPUTABLE: `decAccessTypingClean` is a
-- correct-by-construction checker derivable from the spec itself, whose
-- `Yes` carries the full acceptance proof and whose `No` carries a refutation.
--
-- This is the concrete sense in which the typing checker can be "moved
-- inside the spec's sight" (collapsing the determine-vs-bound BOUND on the
-- typing LOGIC): the decision procedure IS a verifier, verified. After this,
-- the residual trust is decode-faithfulness ALONE — producing the `SpecSite`
-- data from wasm bytes — with no trust remaining in the typing decision. Full
-- extraction-to-Rust and the wasm operational-semantics (WasmCert) tie-back
-- remain the open, multi-week T5 tail; this is its verified kernel.

||| The spec's per-site acceptance is decidable: a `Yes` builds the
||| `SiteWellTyped` witness, a `No` refutes one of its three conjuncts.
export
decSiteWellTyped : (s : SpecSite) -> Dec (SiteWellTyped s)
decSiteWellTyped s =
  case decEq (opMatchesField (siteOp s) (siteField s)) True of
    No nm => No (\(MkSiteWellTyped m _ _) => nm m)
    Yes m => case decEq (siteOffset s) (siteFieldOff s) of
      No no => No (\(MkSiteWellTyped _ o _) => no o)
      Yes o =>
        case isLTE (siteFieldOff s + packedScalarSize (siteField s)) (siteRegionSz s) of
          No nl => No (\(MkSiteWellTyped _ _ l) => nl l)
          Yes l => Yes (MkSiteWellTyped m o l)

||| The whole-list acceptance criterion is decidable — the verified,
||| extractable access-typing checker. Running it on the sites the Rust
||| pass decodes is the data-level cross-check the bound reduces to.
export
decAccessTypingClean : (sites : List SpecSite) -> Dec (AccessTypingClean sites)
decAccessTypingClean = all decSiteWellTyped
