# Proof Debt Status

**What's mechanically proven in typed-wasm, what's outstanding, and what's blocked on prerequisites.**

This page is for readers asking _"where is the theorem?"_ when faced with typed-wasm's safety claims. The proofs live in `src/abi/TypedWasm/ABI/*.idr` and are mechanically checked by Idris2 0.8.0. The detailed inventory lives in [`PROOF-NEEDS.md`](https://github.com/hyperpolymath/typed-wasm/blob/main/PROOF-NEEDS.md) and [`LEVEL-STATUS.md`](https://github.com/hyperpolymath/typed-wasm/blob/main/LEVEL-STATUS.md); this page summarises and links.

## Invariants

- **0 `believe_me`** in the checked package
- **0 `assert_total`** in the checked package
- **0 `postulate`** in the checked package
- **0 `sorry`** / **0 `Admitted`** in the checked package
- **0 `assert_smaller`** in the checked package
- **`%default total`** everywhere

Verified by `tests/proof/regression.mjs` (107 named-theorem grep assertions) and by `idris2 --build src/abi/typed-wasm.ipkg` (22/22 modules under Idris2 0.8.0).

## The proof package

22 Idris2 modules. Per-module status is in `LEVEL-STATUS.md` §"Proof inventory"; the headline:

| Module | Role |
|---|---|
| `Region.idr` | Schema + FieldIn (L1, L2, L5 structural primitives) |
| `TypedAccess.idr` | Typed load/store + AccessResult (L3, L6) |
| `Levels.idr` | Canonical L1-L10 data types |
| `Pointer.idr` | Pointer kinds + ExclusiveWitness (L4, L7) |
| `Effects.idr` | Effect-set + subsumption (L8) |
| `Lifetime.idr` | Outlives preorder + load-safety (L9) |
| `Linear.idr` | CompletedProtocol + linear discipline (L10) |
| `MultiModule.idr` | Schema-subtype + no-spoofing theorem (cross-module) |
| `Tropical.idr` | Cost-bounded paths (L11, draft) |
| `Epistemic.idr` | Freshness propagation (L12, draft) |
| `ModuleIsolation.idr` | Per-module memory isolation (L13) |
| `SessionProtocol.idr` | Session protocols + WellFormedProtocol (L14) |
| `ResourceCapabilities.idr` | Capability lattice (L15) |
| `Choreography.idr` | Composition over L13+L14+L15 (L16) |
| `Layout.idr` + `Layout/*.idr` | Cross-language layout contracts |
| `Echo.idr` | Echo composition (research) |
| `Proofs.idr` | Top-level certificate assembly + witness-indexed attestation API + WitnessCertificate lift |
| **`VerifierSpec.idr`** | **Spec-of-record for the Rust post-codegen verifier (added 2026-05-27 via PR #79)** |

## Recently closed (2026-05-27 sweep)

The 2026-05-18 PROOF-NEEDS reconciliation banner deferred several long-tail items. A 2026-05-27 sweep closed three of them:

### Item 7 + Item 8 — Verifier ↔ spec ↔ source agreement (PR #79)

The post-A10 audit (item 7: Rust verifier ↔ Idris2 spec equivalence; item 8: source-checker ↔ verifier coverage agreement) stated two record obligations:

```idris
record VerifierSpecAgreement where
  constructor MkVerifierSpecAgreement
  verifierIsSound    : (m : ModuleSummary) -> VerifierAccepts m -> SpecAccepts m
  verifierIsComplete : (m : ModuleSummary) -> SpecAccepts m -> VerifierAccepts m

record SourceVerifierAgreement where
  constructor MkSourceVerifierAgreement
  sourceImpliesVerifier : (m : ModuleSummary) -> SourceAccepts m -> VerifierAccepts m
  verifierImpliesSource : (m : ModuleSummary) -> VerifierAccepts m -> SourceAccepts m
```

PR #74 attempted these with `Maybe`-returning bridges and a closed-world `RegisteredFixture` GADT, but the records themselves remained uninhabited — #74 explicitly called this "the multi-week residual".

**PR #79 closes the bodies** by refactoring the differential constructor to carry the structural witness inline:

```idris
data VerifierAccepts : ModuleSummary -> Type where
  VAStructural   : FunctionsAccepted m.functions -> VerifierAccepts m
  VADifferential : (fixture : TrustedFixture m)  -> VerifierAccepts m

record TrustedFixture (m : ModuleSummary) where
  constructor MkTrustedFixture
  trustedFixtureName : String
  trustedFixtureId   : Nat
  trustedWitness     : FunctionsAccepted m.functions
```

The trust-injection moment moves to `MkTrustedFixture` construction (single grep point for audit). All four agreement lemmas become total by case analysis. `verifierSpecAgreement : VerifierSpecAgreement` and `sourceVerifierAgreement : SourceVerifierAgreement` are concrete inhabitants — the first total no-`believe_me` agreement values in the codebase.

End-to-end demo on cross_compat row 1 (`fixtureCleanLinearConsumerModule`). Four discrimination proofs show L10 has teeth and the differential escape hatch cannot smuggle a bad module past the verifier.

### standards#130 — LevelAttestation reindexed-by-witness (PR #80)

The 2026-05-18 banner flagged:

> "Stronger 'attestation entails the level's semantic property' (needs `LevelAttestation` reindexed by witness) remains tracked future work under standards#130."

The A9 work proved `LevelAchievedIn N [attestLN_X w]` — i.e. "the certificate provably claims level N". But that's the weaker face: anyone holding the attestation cannot recover the underlying witness (`ExclusiveWitness s` for L7, etc.) because the legacy `attestLN_*` family discards it.

**PR #80 closes this** with a witness-indexed GADT:

```idris
data LevelAttestationW : (n : Nat) -> Type where
  AttestL7W : {s : Schema} -> (w : ExclusiveWitness s) -> LevelAttestationW 7
  -- … 14 more constructors, one per level

attestL7W_EntailsAliasFree :
     LevelAttestationW 7
  -> (s : Schema ** ExclusiveWitness s)
attestL7W_EntailsAliasFree (AttestL7W {s} w) = (s ** w)
```

A consumer holding `LevelAttestationW 7` can now discharge the L7 semantic property (alias-freeness via `ExclusiveWitness s`) — not just the weak claim-predicate. Purely additive: legacy `LevelAttestation`, `MkAttestation`, `attestLN_*`, `attestLN_Sound`, `LevelAchievedIn`, `composeCertificates`, `ProofCertificate` are all unchanged. 15 ctors + 15 smart ctors + 15 extractors + legacy bridge + 15 round-trip `Refl`s + uniform `attestLW_AchievedIn` (subsuming the A9 family).

### WitnessCertificate — heterogeneous-list lift (PR #80, folded from #83)

`LevelAttestationW n` retains the witness per attestation, but `ProofCertificate` still uses `List LevelAttestation` for its `levels` field, so a heterogeneous certificate can't be built directly. **PR #83 (folded into #80)** adds an existential wrapper:

```idris
data SomeAttestationW : Type where
  MkSomeAttW : {n : Nat} -> (att : LevelAttestationW n) -> SomeAttestationW

record WitnessCertificate where
  constructor MkWitnessCert
  witnessLevels        : List SomeAttestationW
  witnessHighestProven : Nat
  witnessMultiModule   : List CompatCertificate

witnessToLegacy : WitnessCertificate -> ProofCertificate
composeWitness  : WitnessCertificate -> WitnessCertificate -> WitnessCertificate
WitnessAchieved : (n : Nat) -> WitnessCertificate -> Type
```

The `composeWitnessLegacyAgree` lemma pins down: composing the legacy projections equals projecting the witness composition — the two paths stay consistent.

## Outstanding long-tail items

In rough decreasing priority:

### Verifier L1–L6 + L13–L16 coverage on emitted wasm (#34 / #35)

**Status:** in progress on PRs #76 (carrier-section wire-format proposal) + #77 (L2 codec pre-staged behind `cfg(feature = "unstable-l2")`). DO NOT interfere — actively worked by a parallel session.

The Rust verifier currently covers L7 (aliasing) + L10 (linearity) only. Extending it requires a multi-producer ABI change: a new custom section for L2-L6 region/field schema + nullability + cardinality, and another for the L15 capability lattice. Coordinated across `hyperpolymath/{typed-wasm,ephapax,affinescript}`.

### WasmCert-Isabelle tie-back

**Status:** not started. Tracked in `docs/supplementary/proof-inventory.adoc:45`, `docs/WHITEPAPER.md:602`, `LEVEL-STATUS.md:66`. Requires external Isabelle/HOL artifact + bridge; multi-week. The goal is to connect typed-wasm's `Region.idr` semantics to the WasmCert mechanised operational semantics so the L1-L6 claims can be discharged against a reference wasm semantics, not just paper-equivalents.

### Emitted-wasm byte-equality (P3.1(a))

**Status:** blocked on emitter. PROOF-NEEDS.md:442 explicitly says: "blocked pending a `.twasm`→`.wasm` emitter". Once an emitter lands, extend `tests/echidna/echidna-harness.mjs` Property 5 to run both sides through the emitter and `assertBytesEqual`.

### Parser round-trip in Idris2

**Status:** blocked on parser port. The AffineScript parser is OCaml (`lib/ocaml/Parser.affine`). The ECHIDNA-side fuzz property is doable today; the Idris2 mechanical proof is blocked on the Track A AffineScript→Idris2 parser port.

## How the proofs relate to runtime safety

| Layer | What it proves | Where |
|---|---|---|
| **Idris2 proofs** | Type discipline is sound (spec-level): every well-typed program respects L1-L10 / L13-L16 | `src/abi/TypedWasm/ABI/*.idr` |
| **Source checker** | Source programs respect the discipline | `hyperpolymath/affinescript:lib/codegen.ml` (QTT pass), upcoming `.twasm` parser/checker |
| **Post-codegen verifier** | Emitted wasm bytes respect the discipline (covers L7 + L10 today) | `crates/typed-wasm-verify/` (Rust) + `hyperpolymath/affinescript:lib/{tw_verify,tw_interface}.ml` (OCaml, reference impl) |
| **Spec-of-record (2026-05-27)** | Verifier and source-checker agree with the Idris2 spec — bundled as totally-proven records | `src/abi/TypedWasm/ABI/VerifierSpec.idr` (NEW) |

The agreement records introduced in PR #79 close the loop: a drift between the Rust verifier's accept-verdict on a fixture and the Idris2 spec's `SpecAccepts` predicate now shows up either as a failing differential-harness fixture or as an absent `TrustedFixture` registration. Trust is injected once per audited fixture, not at every consumer.

## Build and test oracle

```bash
# Build the proof package
IDRIS2_PREFIX=$IDRIS2/0.8.0 idris2 --build src/abi/typed-wasm.ipkg
# expects: 22/22 modules, rc=0

# Run the proof regression
PATH=$IDRIS2/0.8.0/bin:$PATH \
IDRIS2_PREFIX=$IDRIS2/0.8.0 \
  deno run --allow-read --allow-write --allow-run --allow-env --allow-sys tests/proof/regression.mjs --strict
# expects: 107 passed, 0 failed, 0 skipped

# Verify no banned patterns
grep -rnE "believe_me|assert_total|postulate|sorry|Admitted|assert_smaller" \
  src/abi/TypedWasm/ABI/*.idr \
  | grep -vE "^[^:]+:[0-9]+:--|^[^:]+:[0-9]+:[[:space:]]*--|^[^:]+:[0-9]+:\|\|\|"
# expects: no output (only banner comments mention banned patterns)
```

## See also

- [`PROOF-NEEDS.md`](https://github.com/hyperpolymath/typed-wasm/blob/main/PROOF-NEEDS.md) — full per-obligation inventory with reconciliation banners
- [`LEVEL-STATUS.md`](https://github.com/hyperpolymath/typed-wasm/blob/main/LEVEL-STATUS.md) — per-module believe_me / postulate / assert_total status + post-codegen verifier coverage
- [`docs/supplementary/proof-inventory.adoc`](https://github.com/hyperpolymath/typed-wasm/blob/main/docs/supplementary/proof-inventory.adoc) — paper-facing summary
- [`CHANGELOG.md`](https://github.com/hyperpolymath/typed-wasm/blob/main/CHANGELOG.md) — dated PR landings
- [Phase-0-Status](Phase-0-Status) — Phase 0 engineering surface (orthogonal to proof debt)
- [Production-Path](Production-Path) — the 6-phase plan
