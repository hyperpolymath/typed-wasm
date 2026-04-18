# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

**Scope:** handoff document for the Claude instance that will deepen
typed-wasm's formal verification. Read this file in full before
touching `src/abi/TypedWasm/ABI/*.idr`. Written 2026-04-13 by the
dual-AST / parser-panic cleanup Claude after a targeted audit.

## The one-line honest summary

typed-wasm has **eleven Idris2 files encoding a safety protocol using
QTT linearity and dependent types, zero dangerous patterns, but almost
no explicit theorems** — most of the guarantees are structural
consequences of the type encoding rather than propositions that have
been stated and mechanically proven. `Proofs.idr` ceremonially
rubber-stamps attestations without using their witnesses. The next
Claude's job is to close the gap between "the types forbid it at
compile time" (true) and "here is a lemma proving it is forbidden"
(mostly absent). The distinction matters for publication-quality
claims — a reviewer asking _"where is the theorem?"_ currently has no
answer to point at.

## Inventory snapshot (2026-04-13)

- 11 `.idr` files, 2,589 LOC total, `%default total` everywhere, zero
  `believe_me` / `assert_total` / `postulate` / `sorry`.
- 9 files are in `typed-wasm.ipkg` (Region, TypedAccess, Levels,
  Pointer, Effects, Lifetime, Linear, MultiModule, Proofs) + Layout
  aggregate.
- 2 files are **draft only** and standalone `idris2 --check` fails:
  `Tropical.idr`, `Epistemic.idr`. They are NOT in the ipkg. Fix them
  before claiming L11/L12.
- Structure: mostly `data` declarations + constructor helpers. No
  `record` except in Region (RegionSchema) and Tropical (CostAnnotated).
  Zero theorem statements of the form `lemma : P -> Q -> R` that
  manipulate witnesses to prove properties.
- `LEVEL-STATUS.md` line 28 correctly labels L7-L10 as **"Proven
  [sfap], erased"** where "[sfap]" = "so far as possible". That is the
  honest status. L11-L12 are "draft only; not in package; standalone
  check currently fails".

## The proof-writing priority order

Ordered by _dependability > security > interop > usability >
performance > versatility > functional extension_ per estate standing
order. Every item below names a file, a theorem to state, and a
rough difficulty.

### P0 — Dependability (existence proofs for the structural claims)

**P0.1. Tropical semiring laws — Tropical.idr.** The eight axioms of
a commutative semiring with zero. 007 has done this work already in
`proofs/idris2/TropicalSemiring.idr` (12 theorems, CLEAN, zero
`believe_me`). Port it. Specifically prove:

```
tropAddAssoc     : (a, b, c : TropCost) -> tropAdd (tropAdd a b) c = tropAdd a (tropAdd b c)
tropAddComm      : (a, b : TropCost) -> tropAdd a b = tropAdd b a
tropAddIdent     : (a : TropCost) -> tropAdd Infinity a = a
tropMulAssoc     : (a, b, c : TropCost) -> tropMul (tropMul a b) c = tropMul a (tropMul b c)
tropMulComm      : (a, b : TropCost) -> tropMul a b = tropMul b a
tropMulIdent     : (a : TropCost) -> tropMul (Finite 0) a = a
tropMulAnnihil   : (a : TropCost) -> tropMul Infinity a = Infinity
tropDistrib      : (a, b, c : TropCost) -> tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c)
```

Hardest one is distributivity — in min-plus you need `a + min(b,c) =
min(a+b, a+c)`, which requires case analysis on Nat.  Use the 007
versions as templates.

**Also fix the standalone check failure.** File does not currently
type-check on its own. Investigate why (likely a missing import or a
dependent type that isn't reduced) before writing new theorems.
Getting it into `typed-wasm.ipkg` is the entry ticket for L11.

**Difficulty:** medium. Bulk of the work is Nat-arithmetic case
splits. The 007 file is 333 LOC and clean, so it's a rehearsed path.

**P0.2. Linear.idr — explicit consumption theorem.** The file says
"double-free is impossible by construction" in a comment, then
declares a nullary data type `NoDoubleFree` as a "witness". This is
documentation, not a proof. Replace with:

```
||| A linear handle, once consumed, cannot be consumed again.
||| This is the central safety property of Level 10.
linearConsumedOnce : (1 h : LinHandle token) ->
                     (after : FreeResult) ->
                     (freeRegion h live = after) ->
                     -- Cannot produce a second FreeResult from h.
                     Void
```

The exact shape depends on how you model "cannot produce" — QTT's
erased `(0 _ : X)` won't give you the negation. The cleanest approach
is a **usage-counter encoding**:

```
data Usage : Type where
  Fresh    : Usage
  Consumed : Usage

data LinHandleU : (u : Usage) -> (token : Nat) -> Type where
  MkFresh : (off : Nat) -> (sid : Nat) -> LinHandleU Fresh token

consume : LinHandleU Fresh token -> (LinHandleU Consumed token, Nat)
-- then prove: no function Type -> LinHandleU Fresh token exists
-- that produces a fresh handle from a consumed one.
```

Then prove `noReuse : LinHandleU Consumed t -> LinHandleU Fresh t ->
Void`. That is the actual theorem behind the protocol.

**Difficulty:** medium-hard. The nullary `NoDoubleFree` needs real
witness manipulation. Budget a session.

**P0.3. Lifetime.idr — Outlives is a preorder.** File declares
`Outlives : Lifetime -> Lifetime -> Type` as an abstract relation. The
safety of `LiveRef` depends on `Outlives` being at least reflexive and
transitive. Prove:

```
outlivesRefl  : (l : Lifetime) -> l `Outlives` l
outlivesTrans : l1 `Outlives` l2 -> l2 `Outlives` l3 -> l1 `Outlives` l3
```

Then the **load-safety theorem**, which is the actual L9 guarantee:

```
loadSafe : (ref : LiveRef lref a) ->
           (scope : RegionLife token) ->
           (p : scope `Outlives` lref) ->
           -- dereferencing in this scope produces a well-typed a
           a
```

Currently `LiveRef` extracts its offset and hopes for the best.
`loadSafe` is the proof that the hope is justified.

**Difficulty:** medium. Depends on how `Outlives` is defined — if it's
just an opaque type, you have to add constructors first.

**P0.4. Effects.idr — EffectSubsumes preorder + monotonicity.**
`Proofs.idr:171` shows `attestL8_EffectSafe : EffectSubsumes declared
actual -> LevelAttestation` which takes a witness and discards it.
For this attestation to mean anything, `EffectSubsumes` must be a
real preorder:

```
subsumeRefl  : (es : List Effect) -> EffectSubsumes es es
subsumeTrans : EffectSubsumes xs ys -> EffectSubsumes ys zs -> EffectSubsumes xs zs
```

Plus the composition theorem — when you sequence two operations, the
combined effect set is the union and the subsumption is preserved:

```
subsumeCompose : EffectSubsumes d1 a1 -> EffectSubsumes d2 a2 ->
                 EffectSubsumes (d1 ++ d2) (a1 ++ a2)
```

Otherwise L8 is a fiction — a correct-looking attestation with no
content. `SubNil` is referenced in `Proofs.idr:239` but I did not
find its definition; verify it exists and strengthen it if it does
not.

**Difficulty:** easy-medium if `EffectSubsumes` has concrete
constructors, hard if it has to be redesigned.

**P0.5. MultiModule.idr — CompatCertificate reflexivity + transitivity
+ composition. ✅ DONE 2026-04-18 (A6).**

The strengthened propositional layer was added to MultiModule.idr alongside
the existing data declarations (none of which were rewritten).  The new
relation `ModuleCompat` is indexed by both modules *and* schemas, which
avoids the "compatCommute implicit bidirectionality" question: the schema
order pins the direction of the subschema witness.

Proved:

```
compatRefl  : (m : ModuleId) -> (s : Schema) -> ModuleCompat m m s s
compatTrans : ModuleCompat m1 m2 s1 s2 -> ModuleCompat m2 m3 s2 s3
           -> ModuleCompat m1 m3 s1 s3
```

plus the flagship no-spoofing theorem:

```
noSpoofing : ModuleCompat from to imp exp
          -> (f : Field) -> FieldMatches f imp
          -> FieldMatches f exp
```

and a type-preservation corollary `noTypeSpoofing` at a known
`(name, ty)` pair.  The work-horse lemma is `fieldMatchesLift :
FieldMatches f y -> SchemaSub y z -> FieldMatches f z`, which walks
the SchemaSub witness field-by-field — so the proof is not vacuous.

Sanity-checked with a worked Rust-exports / ReScript-imports example
(4-field export `[id: U64, age: U8, score: F32, banned: WBool]`,
2-field subset import `[id: U64, age: U8]`) that constructs a live
`ModuleCompat` certificate and applies `noSpoofing` to it.  Zero
`believe_me` / `assert_total` / `postulate` / `sorry`; `%default
total` preserved.

`compatCommute` is NOT proven because it only holds when the two
subschema relations are mutually witnessed — at that point the two
schemas are equal up to reordering and the commutativity is a
one-line corollary of `noSpoofing` in both directions.  Left as
future work only if a downstream consumer actually needs it.

**Original task description preserved for history:** File has 12
`data` declarations describing cross-module memory compatibility.
Prove:

```
compatRefl   : (m : ModuleId) -> Compat m m
compatTrans  : Compat m1 m2 -> Compat m2 m3 -> Compat m1 m3
compatCommute : Compat m1 m2 -> Compat m2 m1   -- if bidirectional
```

Plus the **no-spoofing theorem**: if `Compat m1 m2` holds, then every
region accessible from `m1` is either exported by `m1` or imported
from a module compatible with `m1`. This is the actual multi-module
memory safety invariant — the paper's killer feature. If you can
state and prove this one, typed-wasm has a real story to tell.

**Difficulty:** hard. This is the flagship theorem. Budget multiple
sessions. Consider writing a small example multi-module program first
to sanity-check the statement before proving it.

### P1 — Security (the parts where ceremony ≠ evidence)

**P1.1. Replace every ceremonial attestation in `Proofs.idr` with
evidence-consuming versions. ✅ DONE 2026-04-18 (A7).**

Every nullary attestation in `Proofs.idr` has been promoted to require
a witness from its level's proof module:

| Attestation | Witness type | Source module |
|---|---|---|
| `attestL1_InstructionValid` | `Schema` | Region.idr |
| `attestL2_RegionBound` | `FieldIn name schema` | Region.idr |
| `attestL3_TypeCompat` | `WasmTypeCompat a b` | MultiModule.idr |
| `attestL4_NullSafe` | `Pointer.Ptr k s l NonNull` | Pointer.idr |
| `attestL5_BoundsProof` | `InBounds idx count` | Region.idr |
| `attestL6_ResultType` | `AccessResult ty` | TypedAccess.idr |
| `attestL7_AliasFree` | `ExclusiveWitness s` | Pointer.idr |
| `attestL8_EffectSafe` | `EffectSubsumes declared actual` | Effects.idr (pre-existing) |
| `attestL9_LifetimeSafe` | `Lifetime.Outlives rl sl` | Lifetime.idr |
| `attestL10_Linear` | `CompletedProtocol tok` | Linear.idr |

`simpleReadCert`, `fullCert12`, and `fullCert15` now thread each of the
required witnesses through their signatures.  The top-level certificate
cannot be constructed without a proof term for every level it claims.

Qualification note: `Lifetime` and `Outlives` are resolved as
`Lifetime.Lifetime` / `Lifetime.Outlives` (from Lifetime.idr), while
`Pointer.Ptr`'s lifetime parameter takes `Levels.Lifetime` (which is
what Pointer.idr itself imports from Levels.idr).  A small comment in
Proofs.idr explains the qualification; both `Lifetime` types remain
in the codebase for now.

**Original task description preserved for history:** Current state:

```
attestL10_Linear : LevelAttestation
attestL10_Linear = MkAttestation 10 Proven
```

Takes no arguments — anyone can call it. Should be:

```
attestL10_Linear : (p : LinearProof t) -> LevelAttestation
attestL10_Linear _ = MkAttestation 10 Proven
```

where `LinearProof t` is a real proof-carrying type (built on P0.2).
Same treatment for `attestL9_LifetimeSafe` (should require a
`LoadSafe` witness), `attestL7_AliasFree` (should require a `Unique`
witness from Pointer.idr), `attestL3_TypeCompat`, etc. The whole
point of a certificate is that you cannot construct it without the
underlying proofs.

**Difficulty:** mechanical once P0.1–P0.4 land. Do it immediately
after each P0 completes.

**P1.2. Epistemic.idr — fix standalone check, then prove Level12Proof
implies freshness.** Draft-only. First make it type-check in
isolation (figure out the missing imports / unresolved variables),
then state:

```
Level12Proof : (writer : Commit) -> (reader : View) -> Type
-- constructor requires view.timestamp >= commit.timestamp

epistemicFreshness : Level12Proof w r -> (LTE (commitTimestamp w) (viewTimestamp r))
```

Currently the existence of `Level12Proof` is waved through by
`attestL12_EpistemicFresh _ = MkAttestation 12 Proven`. As with P0.2
and P1.1, the actual theorem has to be written down.

**Difficulty:** medium once the file type-checks. Getting it to
type-check is the hard bit — may require understanding a design
decision that the draft obscures.

**P1.3. Region.idr — schema injectivity. ✅ DONE 2026-04-18 (A8) —
reframed for current Schema = List Field design.**

The original P1.3 asked for `schemaIdInjective` over a
`RegionSchema` record with a `schemaId : Nat`.  That record does not
exist in the current codebase — a Schema is just a `List Field`,
identified structurally.  The equivalent L2 soundness claims at the
current design are proven in Region.idr:

```
fieldNameInj    : MkField n1 t1 = MkField n2 t2 -> n1 = n2
fieldTypeInj    : MkField n1 t1 = MkField n2 t2 -> t1 = t2
fieldInj        : MkField n1 t1 = MkField n2 t2 -> (n1 = n2, t1 = t2)
schemaEqSym     : SchemaEq s1 s2 -> SchemaEq s2 s1
schemaEqTrans   : SchemaEq s1 s2 -> SchemaEq s2 s3 -> SchemaEq s1 s3
lookupFieldName : (prf : FieldIn name schema)
                -> fieldName (lookupField prf) = name
```

Together with the pre-existing `schemaEqRefl`, these make `SchemaEq`
a full equivalence relation and pin down "same structural identifier
implies same schema" at the Idris2 level.  `lookupFieldName` closes
the L2 soundness gap: having a `FieldIn` witness guarantees the
extracted field really answers to the looked-up name.

**Original task description preserved for history:** If two schemas have the
same `schemaId : Nat`, they are the same schema. This is required for
the L2 guarantee (region-binding) to be sound:

```
schemaIdInjective : (s1, s2 : RegionSchema) ->
                    schemaId s1 = schemaId s2 ->
                    s1 = s2
```

Without this, an attacker can mint two schemas with the same ID and
confuse the typed-access layer. If `RegionSchema` is a record then
you need decidable equality on every field.

**Difficulty:** easy if `RegionSchema` is simple, medium if it has
nested List/Map fields.

### P2 — Interop (parser + round-trip, ECHIDNA coverage)

**P2.1. Parser round-trip property.** ReScript parser in
`lib/ocaml/Parser.res` / `Lexer.res` / `Ast.res`. The ECHIDNA runs
listed in `LEVEL-STATUS.md` are for runtime L1-L6; there is no
property-based test asserting `parse (print ast) = Right ast`. Add
one. This is not an Idris2 proof — it's an ECHIDNA generator + a
fuzz run at 10^5 or higher. Until the parser is ported to Idris2, the
formal-proof version is not available, but the ECHIDNA check is cheap
and catches round-trip bugs immediately.

**Difficulty:** easy.

**P2.2. Parser produces well-formed modules.** Similar — state that
every successful parse yields an AST satisfying a `WellFormed`
predicate (no dangling region refs, no unbound locals, all function
indices in range). Can be an ECHIDNA predicate today and a mechanical
proof once the parser ports to Idris2.

**Difficulty:** easy.

### P3 — Usability / performance / versatility

**P3.1. Erasure guarantee formalization.** `ProofErasureGuarantee` in
`Proofs.idr:264` is a nullary data type. The real claim is:
"compiling a proof-carrying typed-wasm program produces byte-for-byte
identical WASM output to the equivalent hand-written program". This
is a meta-theorem about the Idris2 compiler's QTT erasure, not a
theorem inside Idris2. Two ways to attack it:

  (a) **Property-based**: diff the `.wasm` output of a proof-carrying
      module against a hand-written module, assert byte equality.
      ECHIDNA can generate both sides. This is what the paper should
      cite today.

  (b) **Meta-theoretic**: appeal to Idris2's QTT erasure spec and
      write a short ADR explaining the reduction. This is future
      work.

**Difficulty:** (a) easy, (b) requires reading Brady & Christiansen's
QTT paper and citing it.

**P3.2. Levels progression monotonicity. ✅ DONE 2026-04-18 (A8) —
reframed for current ProgressiveCheck / ProofCertificate design.**

The original P3.2 asked for `levelMonotone : LevelAchieved n -> LTE
m n -> LevelAchieved m` over a `LevelAchieved` predicate that does
not exist in the codebase.  Under the current design, the
structural monotonicity relevant at the Idris2 level is
*composition preservation*, proven in Proofs.idr:

```
LevelAchievedIn : (n : Nat) -> List LevelAttestation -> Type
  LAHere  : LevelAchievedIn n (MkAttestation n Proven :: rest)
  LAThere : LevelAchievedIn n rest -> LevelAchievedIn n (att :: rest)

achievedAppendL : LevelAchievedIn n xs  -> LevelAchievedIn n (xs ++ ys)
achievedAppendR : LevelAchievedIn n ys  -> LevelAchievedIn n (xs ++ ys)

LevelAchieved : Nat -> ProofCertificate -> Type
  -- lifted from LevelAchievedIn over the certificate's attestations

composeAchievedL : LevelAchieved n c1 -> LevelAchieved n (composeCertificates c1 c2)
composeAchievedR : LevelAchieved n c2 -> LevelAchieved n (composeCertificates c1 c2)
```

A level achieved in either component of a `composeCertificates`
combination is still achieved in the composition.  The stronger
"progressive-order" claim — achieving level N implies all lower
levels hold — would require redesigning `ProgressiveCheck` with a
typed `level = S prevLevel` invariant.  That redesign is left as
future work; the composition monotonicity above is the useful
structural claim at the current design.

**Original task description preserved for history:** If a program achieves
Level N, it achieves all levels 1..N. Stated as:

```
levelMonotone : LevelAchieved n -> (m : Nat) -> LTE m n -> LevelAchieved m
```

Currently `ProgressiveCheck` in `Proofs.idr` sort of encodes this
operationally but does not prove the monotonicity as a theorem.

**Difficulty:** easy once you add a `LevelAchieved` predicate.

## What NOT to do

- **Don't rewrite the existing files.** The data encodings are
  thoughtful and the comments are valuable. Add theorems alongside
  them, don't replace them.
- **Don't start from Tropical or Epistemic.** Those are the draft
  files. Fix the standalone check as preliminary work but do not
  pour proof effort into them until they compile.
- **Don't try to prove erasure inside Idris2** — it is a property of
  the compiler, not the language. P3.1 documents the correct
  approach.
- **Don't conflate structural and propositional claims.** "QTT
  enforces single consumption" is a structural claim (true); "`forall
  h. consumed h -> consumed h -> Void`" is a theorem (currently
  unproven). The paper should distinguish these.
- **Don't add `believe_me`, `assert_total`, `postulate`, or `sorry`.**
  The zero-dangerous-pattern inventory is a selling point. Preserve
  it.
- **Don't reach for Lean4 or Coq.** Idris2 is the right prover for
  this codebase per the estate rule (Idris2 is the preferred proof
  backend). Staying in-tree keeps the proof toolchain singular.

## Recommended session sequence

1. **Session 1** — fix `Tropical.idr` and `Epistemic.idr` standalone
   checks. Get both into `typed-wasm.ipkg`. Commit as a single
   infrastructure fix.
2. **Session 2** — port TropicalSemiring axioms from 007. This is
   low-risk rehearsed work and gives the proof harness a workout.
3. **Session 3** — Linear.idr consumption theorem (P0.2). This is
   the real L10 guarantee.
4. **Session 4** — Lifetime.idr `Outlives` preorder + `loadSafe`
   (P0.3). L9.
5. **Session 5** — Effects.idr `EffectSubsumes` preorder + compose
   (P0.4). L8.
6. **Session 6** — MultiModule.idr CompatCertificate preorder +
   no-spoofing theorem (P0.5). The flagship. May run long; split if
   needed.
7. **Session 7** — Replace every ceremonial attestation in
   `Proofs.idr` with evidence-consuming variants (P1.1). Mechanical
   once P0 is done.
8. **Session 8** — Region.idr injectivity (P1.3), parser ECHIDNA
   (P2.1, P2.2), Levels monotonicity (P3.2). Cleanup session.

After each session: run `idris2 --check` on every file in
`typed-wasm.ipkg`, run `panic-attack assail` on the Rust/ReScript
adjacent code (no new unsafe code should land), update this file's
inventory table, commit.

## Outstanding infrastructure work — Layout module fix (added 2026-04-18)

`Layout/Types.idr` was never compiling cleanly under this Idris2 0.8
build.  The directory rename `layout/` → `Layout/` (filesystem case
matching the `Layout.*` module names) and the `import layout.Types`
→ `import Layout.Types` typo fix in `TypedWasm/ABI/Layout.idr` were
made on 2026-04-18, which surfaced the underlying issues:

  1. **Mutual recursion not declared.**  `WasmHeapType` references
     `WasmValType` (line 65) but `WasmValType` is declared later
     (line 73).  Wrapping both in `mutual` is needed.
  2. **Visibility annotations missing.**  `data WasmPrimitive` /
     `WasmHeapType` / `WasmValType` and the layout values
     (`stringLayout`, `optionLayout`, `resultLayout`, `enumLayout`,
     `recordLayout`) all lack `public export`, so downstream
     constructors are not visible and `Refl`-based proofs do not
     unify.
  3. **Imports missing.**  `Decidable.Equality` is used (`DecEq`,
     `Yes`, `No`, `decEq`) but never imported; `Data.List` similarly.
  4. **Nested `with` block patterns** in the `DecEq WasmHeapType`
     instance (lines 178-234) trigger pattern-variable unification
     errors under this Idris2 build.
  5. **Refl-impossible patterns** (`stringOptionDistinct _ Refl
     impossible` etc.) need the layout values to reduce at unification
     time — even with `public export` the reduction does not happen
     under this build, so a different proof strategy is needed
     (probably explicit `case ... of` with constructor mismatch).

**Current gating (2026-04-18):** the four `Layout.*` modules are
commented out of `typed-wasm.ipkg` and the `import TypedWasm.ABI.Layout`
line in `TypedWasm/ABI/Proofs.idr` is gated.  This unblocks the full
ipkg build for the typed-wasm core (TypedWasm.ABI.* modules) — which
is the primary purpose of typed-wasm.  The aggregate-library Layout
contracts remain in the tree for restoration once the issues above
are addressed.

**Remediation plan:** add `public export` to every Layout type/value;
add `import Decidable.Equality, Data.List`; rewrite the `DecEq
WasmHeapType` and `DecEq WasmValType` instances without nested `with`
(use case-of or explicit witness construction); replace the
Refl-impossible patterns with `case ... of` + constructor analysis.
Estimated effort: one focused session.

## Pre-existing notes (preserved from prior revision)

### Template ABI Cleanup (2026-03-29)

Template ABI removed -- was creating false impression of formal
verification. The removed files (Types.idr, Layout.idr, Foreign.idr)
contained only RSR template scaffolding with unresolved
project/author template tokens and no domain-specific proofs.
