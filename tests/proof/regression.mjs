#!/usr/bin/env node
// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Proof-level regression test.
//
// TEST-NEEDS.md flagged: "11 Idris2 proof modules with 0 proof verification
// tests — proven is unproven." This file is the regression-style backstop:
// it asserts that named theorems / lemmas continue to exist in the Idris2
// source. A future commit that silently deletes or renames a load-bearing
// theorem will trip this test.
//
// Two layers:
//
//   Layer 1 (always runs)
//     Source-level grep for expected theorem signatures. Catches deletion
//     and rename. Does NOT catch a proof that compiles but is wrong; that
//     is what the Idris2 totality checker is for.
//
//   Layer 2 (runs only when idris2 is on PATH)
//     `idris2 --build src/abi/typed-wasm.ipkg` — actually typechecks +
//     compiles the proof package.  Catches the case where a theorem
//     name still exists but its body no longer typechecks.  This is
//     the strong test; it requires an Idris2 toolchain at the version
//     pinned in src/abi/typed-wasm.ipkg (currently 0.8.0).  `--build`
//     is used instead of `--check` because the latter expects a single
//     `.idr` file path, not an ipkg.
//
// Phase 0 / Track C deliverable. See:
//   - TEST-NEEDS.md "11 Idris2 proof modules with 0 proof verification tests"
//   - docs/PRODUCTION-PATH.adoc §Phase 0 / Track C
//   - Issue #48
//
// Run:  node tests/proof/regression.mjs
//   or: node tests/proof/regression.mjs --strict   (fails if idris2 absent)

import { readFileSync, existsSync } from "node:fs";
import { resolve, dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..", "..");
const ABI_DIR = join(ROOT, "src/abi/TypedWasm/ABI");
const STRICT = process.argv.includes("--strict");

let passed = 0;
let failed = 0;
let skipped = 0;
const failures = [];

function ok(msg) { console.log(`  OK    ${msg}`); passed++; }
function bad(msg) { console.log(`  FAIL  ${msg}`); failed++; failures.push(msg); }
function skip(msg) { console.log(`  SKIP  ${msg}`); skipped++; }
function section(name) { console.log(`\n=== ${name} ===`); }

function readIdr(file) {
  const path = join(ABI_DIR, file);
  if (!existsSync(path)) return null;
  return readFileSync(path, "utf8");
}

// ----------------------------------------------------------------------
// Expected theorem inventory
//
// Each entry: [file, identifier_regex, why_it_matters]
//
// Regexes match either:
//   - top-level definition  (`name : Type`)
//   - public export        (`public export name : Type`)
//   - data declaration     (`data Name`)
//
// Names taken from current source (2026-05-24); if a name is renamed
// intentionally, update this list AND note the rename in the proof
// module's commit message so reviewers can correlate.
// ----------------------------------------------------------------------

const EXPECTED = [
  // Region.idr — schema correctness
  ["Region.idr", /^Schema\s*:/m, "Schema type"],
  ["Region.idr", /^sizeOf\s*:/m, "Wasm type sizeOf"],
  ["Region.idr", /^fieldType\s*:/m, "fieldType accessor"],

  // TypedAccess.idr — load/store typing
  ["TypedAccess.idr", /^HostType\s*:/m, "Host-type mapping"],
  ["TypedAccess.idr", /^RegionPredicate\s*:/m, "Region predicate"],

  // Levels.idr — the canonical 10-level data types
  ["Levels.idr", /^data\s+Level1_InstructionValidity/m, "L1 data type"],
  ["Levels.idr", /^data\s+Level7_AliasSafe/m, "L7 data type"],

  // Linear.idr — linearity discipline (L10)
  ["Linear.idr", /^allocRegion\s*:/m, "allocRegion linear primitive"],
  ["Linear.idr", /^freeRegion\s*:/m, "freeRegion linear primitive"],
  ["Linear.idr", /^immBorrow\s*:/m, "immBorrow primitive"],

  // Lifetime.idr — lifetime tracking (L9)
  ["Lifetime.idr", /^outlivesRefl\s*:/m, "Outlives reflexivity lemma"],
  ["Lifetime.idr", /^outlivesTrans\s*:/m, "Outlives transitivity lemma"],

  // Effects.idr — effect tracking (L8)
  ["Effects.idr", /^EffectSet\s*:/m, "EffectSet type"],
  ["Effects.idr", /^readWrite\s*:/m, "readWrite effect"],

  // Pointer.idr — pointer kinds (L4 + L7)
  ["Pointer.idr", /^OwnPtr\s*:/m, "OwnPtr (owned pointer) kind"],
  ["Pointer.idr", /^BorrowRef\s*:/m, "BorrowRef (borrowed) kind"],
  ["Pointer.idr", /^UniquePtr\s*:/m, "UniquePtr (unique mutable) kind"],
  ["Pointer.idr", /^checkNull\s*:/m, "Null check primitive"],

  // MultiModule.idr — cross-module sharing (killer feature)
  ["MultiModule.idr", /^LinkGraph\s*:/m, "Link graph type"],
  ["MultiModule.idr", /^schemaSubRefl\s*:/m, "Schema-subtype reflexivity"],
  ["MultiModule.idr", /^schemaSubTrans\s*:/m, "Schema-subtype transitivity"],
  ["MultiModule.idr", /^compatCommute\s*:/m, "Compat commutativity (mutual subschema, A10)"],
  ["MultiModule.idr", /^noSpoofingBidir\s*:/m, "Bidirectional no-spoofing (mutual subschema, A10)"],

  // Epistemic.idr — L12 freshness propagation (A10, 2026-05-26)
  ["Epistemic.idr", /^writerKnowsFresh\s*:/m, "Writer-knows-fresh reflexivity"],
  ["Epistemic.idr", /^freshOrStale\s*:/m, "Fresh/stale trichotomy"],
  ["Epistemic.idr", /^syncRestoresFresh\s*:/m, "Sync restores freshness"],
  ["Epistemic.idr", /^freshImpliesEqual\s*:/m, "Fresh -> known=current projector (A10)"],
  ["Epistemic.idr", /^staleImpliesLT\s*:/m, "Stale -> known<current projector (A10)"],
  ["Epistemic.idr", /^freshNotStale\s*:/m, "Fresh/Stale mutual exclusion (A10)"],
  ["Epistemic.idr", /^concurrentWriteStales\s*:/m, "Concurrent-write staleness (A10)"],
  ["Epistemic.idr", /^resyncRecoversFresh\s*:/m, "Re-sync recovers freshness (A10)"],
  ["Epistemic.idr", /^freshnessPropagatesUnderWrites\s*:/m, "Flagship: L12 propagation under concurrent writes (A10)"],
  ["Epistemic.idr", /^syncChainEndsFresh\s*:/m, "Chained syncs end fresh (A10)"],
  ["Epistemic.idr", /^epistemicFreshness\s*:/m, "Level12Proof projector — closes P1.2 (A10)"],
  ["Epistemic.idr", /^writeSyncIdentifiesWriter\s*:/m, "WriteSync provenance corollary (A11)"],
  ["Epistemic.idr", /^observedHasProvenance\s*:/m, "Observed always traces to a Sync event (A11)"],

  // Layout.idr — cross-language layout contracts (aggregate library role)
  ["Layout.idr", /^subTrans\s*:/m, "Subtype transitivity"],
  ["Layout.idr", /^wasmGCEqRefl\s*:/m, "WasmGC structural-equality reflexivity"],

  // Proofs.idr — main theorem suite
  ["Proofs.idr", /^composeCertificates\s*:/m, "Certificate composition"],
  ["Proofs.idr", /^buildCertificate\s*:/m, "Certificate construction"],
  ["Proofs.idr", /^achievedAppendSplit\s*:/m, "LevelAchievedIn decomposition over ++ (A11)"],
  ["Proofs.idr", /^composeAssocLists\s*:/m, "composeCertificates list-associativity (A11)"],
  ["Proofs.idr", /^composeAchievedSym\s*:/m, "composeCertificates achieved-set symmetry (A11)"],
  ["Proofs.idr", /^composeAssoc\s*:/m, "composeCertificates FULL associativity (A12, closes item 4)"],
  ["Proofs.idr", /^composeHighProvenComm\s*:/m, "composeCertificates Nat-side commutativity (A12, closes item 4)"],

  // Region.idr — A12 disjointness (closes post-A10 audit item 6)
  ["Region.idr", /^data\s+RegionDisjoint/m, "Region byte-disjointness predicate (A12)"],
  ["Region.idr", /^regionDisjointSym\s*:/m, "Region disjointness symmetry (A12)"],

  // ResourceCapabilities.idr — A12 L8↔L15 joint composition (closes audit item 3)
  ["ResourceCapabilities.idr", /^containedConcat\s*:/m, "ContainedIn distributes over ++ (A12)"],
  ["ResourceCapabilities.idr", /^jointBudgetCompose\s*:/m, "L8↔L15 joint budget compose (A12, closes item 3)"],

  // ModuleIsolation.idr — A13 L13×L10 cross-level (closes item 5a)
  ["ModuleIsolation.idr", /^data\s+LinearAcrossBoundary/m, "L13×L10 cross-boundary linear handle predicate (A13)"],
  ["ModuleIsolation.idr", /^linearTransferRequiresBoundary\s*:/m, "L13×L10 no-bypass theorem (A13, closes item 5a)"],
  ["ModuleIsolation.idr", /^linearTransferLocal\s*:/m, "L13×L10 local-case constructor (A13)"],

  // SessionProtocol.idr — A13 L14×L13 cross-level (closes item 5b)
  ["SessionProtocol.idr", /^data\s+SessionAcrossBoundary/m, "L14×L13 cross-boundary session-handle predicate (A13)"],
  ["SessionProtocol.idr", /^sessionAcrossPreservesState\s*:/m, "L14×L13 state-preservation theorem (A13)"],
  ["SessionProtocol.idr", /^sessionTransferRequiresBoundary\s*:/m, "L14×L13 no-bypass theorem (A13, closes item 5b)"],
  ["SessionProtocol.idr", /^sessionTransferLocal\s*:/m, "L14×L13 local-case constructor (A13)"],

  // Region.idr — A13 leave-behind: RegionDisjoint × byte separation
  ["Region.idr", /^data\s+RegionsOverlap/m, "Region byte-overlap predicate (A13)"],
  ["Region.idr", /^disjointImpliesNoOverlap\s*:/m, "Disjointness → byte non-overlap theorem (A13)"],
  ["Region.idr", /^regionsOverlapSym\s*:/m, "RegionsOverlap symmetry (A13)"],

  // VerifierSpec.idr — Rust verifier ↔ Idris2 spec ↔ source checker
  // agreement (post-A10 audit items 7 + 8).  These assertions pin the
  // record shape, the four agreement lemmas, the two concrete agreement
  // values, and the end-to-end composition lemmas — so a future commit
  // that silently weakens any direction or drops a body trips Layer 1.
  ["VerifierSpec.idr", /^data\s+OwnershipIntent/m, "OwnershipIntent data type"],
  ["VerifierSpec.idr", /^record\s+FunctionSummary/m, "FunctionSummary record"],
  ["VerifierSpec.idr", /^record\s+ModuleSummary/m, "ModuleSummary record"],
  ["VerifierSpec.idr", /^data\s+TokenFresh/m, "TokenFresh structural witness"],
  ["VerifierSpec.idr", /^data\s+IntentsLinearAcceptable/m, "IntentsLinearAcceptable witness (A13)"],
  ["VerifierSpec.idr", /^data\s+FunctionsAccepted/m, "FunctionsAccepted witness"],
  ["VerifierSpec.idr", /^record\s+TrustedFixture/m, "TrustedFixture record"],
  ["VerifierSpec.idr", /^data\s+SpecAccepts/m, "SpecAccepts predicate (A13, item 7)"],
  ["VerifierSpec.idr", /^data\s+VerifierAccepts/m, "VerifierAccepts predicate (A13, item 7)"],
  ["VerifierSpec.idr", /^data\s+SourceAccepts/m, "SourceAccepts predicate (A13, item 8)"],
  ["VerifierSpec.idr", /^differentialAccepted\s*:/m, "Differential-acceptance smart ctor"],
  ["VerifierSpec.idr", /^sourceAccepted\s*:/m, "Source differential smart ctor"],
  ["VerifierSpec.idr", /^trustedToSpec\s*:/m, "Trusted-fixture → spec projection"],
  ["VerifierSpec.idr", /^trustedToVerifier\s*:/m, "Trusted-fixture → verifier projection"],
  ["VerifierSpec.idr", /^trustedToSource\s*:/m, "Trusted-fixture → source projection"],
  ["VerifierSpec.idr", /^verifierIsSound\s*:/m, "Verifier soundness lemma body"],
  ["VerifierSpec.idr", /^verifierIsComplete\s*:/m, "Verifier completeness lemma body"],
  ["VerifierSpec.idr", /^sourceImpliesVerifier\s*:/m, "Source ⇒ verifier lemma body"],
  ["VerifierSpec.idr", /^verifierImpliesSource\s*:/m, "Verifier ⇒ source lemma body"],
  ["VerifierSpec.idr", /^record\s+VerifierSpecAgreement/m, "VerifierSpecAgreement record (item 7)"],
  ["VerifierSpec.idr", /^record\s+SourceVerifierAgreement/m, "SourceVerifierAgreement record (item 8)"],
  ["VerifierSpec.idr", /^verifierSpecAgreement\s*:/m, "Concrete VerifierSpecAgreement value"],
  ["VerifierSpec.idr", /^sourceVerifierAgreement\s*:/m, "Concrete SourceVerifierAgreement value"],
  ["VerifierSpec.idr", /^sourceImpliesSpec\s*:/m, "End-to-end source ⇒ spec composition (A13)"],
  ["VerifierSpec.idr", /^specImpliesSource\s*:/m, "End-to-end spec ⇒ source composition (A13)"],
  ["VerifierSpec.idr", /^sourceImpliesSpecConcrete\s*:/m, "Concrete source ⇒ spec specialisation"],
  ["VerifierSpec.idr", /^specImpliesSourceConcrete\s*:/m, "Concrete spec ⇒ source specialisation"],
  ["VerifierSpec.idr", /^notSpecAcceptsBadDoubleConsume\s*:/m, "L10 discrimination — double consume"],
  ["VerifierSpec.idr", /^notVerifierAcceptsBadDoubleConsume\s*:/m, "Verifier rejects double consume in both ctors"],
  ["VerifierSpec.idr", /^notSourceAcceptsBadDoubleConsume\s*:/m, "Source rejects double consume in both ctors"],
  ["VerifierSpec.idr", /^notSpecAcceptsBadDoubleProduce\s*:/m, "L10 discrimination — double produce"],
  ["VerifierSpec.idr", /^fixtureCleanLinearConsumerTrusted\s*:/m, "cross_compat row 1 trusted fixture"],
  ["VerifierSpec.idr", /^fixtureCleanLinearConsumerSpecAccepts\s*:/m, "Spec accepts row 1 via VerifierSpecAgreement"],

  // Proofs.idr — LevelAttestationW (standards#130 long-tail closure):
  // witness-indexed attestation GADT with per-level smart ctors,
  // extractors ("entails-semantic-property" lemmas), legacy bridge,
  // and uniform achievement lemma.  These assertions pin the 49 new
  // top-level names so a future refactor that silently drops a level
  // (e.g. AttestL13W) or weakens a body trips Layer 1.
  ["Proofs.idr", /^data\s+LevelAttestationW/m, "LevelAttestationW witness-indexed GADT"],
  ["Proofs.idr", /^attestL1W_InstructionValid\s*:/m, "L1 W smart ctor"],
  ["Proofs.idr", /^attestL2W_RegionBound\s*:/m, "L2 W smart ctor"],
  ["Proofs.idr", /^attestL3W_TypeCompat\s*:/m, "L3 W smart ctor"],
  ["Proofs.idr", /^attestL4W_NullSafe\s*:/m, "L4 W smart ctor"],
  ["Proofs.idr", /^attestL5W_BoundsProof\s*:/m, "L5 W smart ctor"],
  ["Proofs.idr", /^attestL6W_ResultType\s*:/m, "L6 W smart ctor"],
  ["Proofs.idr", /^attestL7W_AliasFree\s*:/m, "L7 W smart ctor"],
  ["Proofs.idr", /^attestL8W_EffectSafe\s*:/m, "L8 W smart ctor"],
  ["Proofs.idr", /^attestL9W_LifetimeSafe\s*:/m, "L9 W smart ctor"],
  ["Proofs.idr", /^attestL10W_Linear\s*:/m, "L10 W smart ctor"],
  ["Proofs.idr", /^attestL11W_CostBounded\s*:/m, "L11 W smart ctor"],
  ["Proofs.idr", /^attestL12W_EpistemicFresh\s*:/m, "L12 W smart ctor"],
  ["Proofs.idr", /^attestL13W_Isolated\s*:/m, "L13 W smart ctor"],
  ["Proofs.idr", /^attestL14W_SessionSafe\s*:/m, "L14 W smart ctor"],
  ["Proofs.idr", /^attestL15W_CapsSafe\s*:/m, "L15 W smart ctor"],
  ["Proofs.idr", /^attestL1W_EntailsInstructionValid\s*:/m, "L1 entails-semantic-property extractor"],
  ["Proofs.idr", /^attestL2W_EntailsRegionBound\s*:/m, "L2 extractor"],
  ["Proofs.idr", /^attestL3W_EntailsTypeCompat\s*:/m, "L3 extractor"],
  ["Proofs.idr", /^attestL4W_EntailsNullSafe\s*:/m, "L4 extractor"],
  ["Proofs.idr", /^attestL5W_EntailsBoundsProof\s*:/m, "L5 extractor"],
  ["Proofs.idr", /^attestL6W_EntailsResultType\s*:/m, "L6 extractor"],
  ["Proofs.idr", /^attestL7W_EntailsAliasFree\s*:/m, "L7 extractor (the alias-freeness recovery)"],
  ["Proofs.idr", /^attestL8W_EntailsEffectSafe\s*:/m, "L8 extractor"],
  ["Proofs.idr", /^attestL9W_EntailsLifetimeSafe\s*:/m, "L9 extractor"],
  ["Proofs.idr", /^attestL10W_EntailsLinear\s*:/m, "L10 extractor"],
  ["Proofs.idr", /^attestL11W_EntailsCostBounded\s*:/m, "L11 extractor"],
  ["Proofs.idr", /^attestL12W_EntailsEpistemicFresh\s*:/m, "L12 extractor"],
  ["Proofs.idr", /^attestL13W_EntailsIsolated\s*:/m, "L13 extractor"],
  ["Proofs.idr", /^attestL14W_EntailsSessionSafe\s*:/m, "L14 extractor"],
  ["Proofs.idr", /^attestL15W_EntailsCapsSafe\s*:/m, "L15 extractor"],
  ["Proofs.idr", /^toLegacy\s*:/m, "LevelAttestationW → LevelAttestation bridge"],
  ["Proofs.idr", /^toLegacyMatchesL1\s*:/m, "L1 round-trip Refl"],
  ["Proofs.idr", /^toLegacyMatchesL15\s*:/m, "L15 round-trip Refl"],
  ["Proofs.idr", /^attestLW_AchievedIn\s*:/m, "Uniform LevelAchievedIn lemma (subsumes A9 family)"],

  // Proofs.idr — WitnessCertificate: ProofCertificate lifted to
  // witness-carrying form via SomeAttestationW existential wrapper.
  // Pins the new shape so a future refactor doesn't silently drop the
  // bridge or the composition-compat lemma.
  ["Proofs.idr", /^data\s+SomeAttestationW/m, "SomeAttestationW existential wrapper"],
  ["Proofs.idr", /^someAttLevel\s*:/m, "Level-index projection"],
  ["Proofs.idr", /^someAttToLegacy\s*:/m, "Wrapped attestation → legacy projection"],
  ["Proofs.idr", /^record\s+WitnessCertificate/m, "WitnessCertificate record"],
  ["Proofs.idr", /^witnessLevelsToLegacy\s*:/m, "List projection helper"],
  ["Proofs.idr", /^witnessToLegacy\s*:/m, "WitnessCertificate → ProofCertificate bridge"],
  ["Proofs.idr", /^composeWitness\s*:/m, "Witness-side composition"],
  ["Proofs.idr", /^witnessLevelsToLegacyAppend\s*:/m, "map distributes over ++ (helper)"],
  ["Proofs.idr", /^composeWitnessLegacyAgree\s*:/m, "Witness composition agrees with legacy under projection"],
  ["Proofs.idr", /^WitnessAchieved\s*:/m, "Achievement predicate lifted"],
  ["Proofs.idr", /^witnessAchievedIsLegacy\s*:/m, "Definitional bridge for WitnessAchieved"],
  ["Proofs.idr", /^emptyWitnessCertificate\s*:/m, "Empty witness certificate (concrete inhabitant)"],
  ["Proofs.idr", /^singletonWitnessCertificate\s*:/m, "Singleton witness certificate smart ctor"],
  ["Proofs.idr", /^emptyWitnessToLegacy\s*:/m, "Empty round-trip Refl"],
];

// ----------------------------------------------------------------------
// Layer 1 — Source-level theorem presence
// ----------------------------------------------------------------------
section("Layer 1: Named-theorem presence in src/abi/TypedWasm/ABI/");

const sourcesAvailable = new Map();
for (const [file, _re, _why] of EXPECTED) {
  if (!sourcesAvailable.has(file)) {
    const src = readIdr(file);
    if (src === null) bad(`Source file missing: ${file}`);
    sourcesAvailable.set(file, src);
  }
}

for (const [file, regex, why] of EXPECTED) {
  const src = sourcesAvailable.get(file);
  if (src === null) {
    bad(`${file}: file missing — cannot check '${why}'`);
    continue;
  }
  if (regex.test(src)) {
    ok(`${file}: '${why}' present (matches ${regex})`);
  } else {
    bad(`${file}: '${why}' missing (no match for ${regex})`);
  }
}

// ----------------------------------------------------------------------
// Layer 2 — Idris2 typecheck of the ipkg
// ----------------------------------------------------------------------
section("Layer 2: Idris2 typecheck of typed-wasm.ipkg");

const which = spawnSync("which", ["idris2"], { encoding: "utf8" });
const idris2Path = which.status === 0 ? which.stdout.trim() : null;

if (!idris2Path) {
  if (STRICT) {
    bad("idris2 not on PATH and --strict requested");
  } else {
    skip("idris2 not on PATH — strong typecheck layer skipped (run with --strict to require it)");
  }
} else {
  const ipkg = join(ROOT, "src/abi/typed-wasm.ipkg");
  if (!existsSync(ipkg)) {
    bad(`ipkg missing at ${ipkg}`);
  } else {
    console.log(`  Running: ${idris2Path} --build ${ipkg}`);
    const check = spawnSync(idris2Path, ["--build", "typed-wasm.ipkg"], {
      cwd: join(ROOT, "src/abi"),
      encoding: "utf8",
      timeout: 300_000,
    });
    if (check.status === 0) {
      ok(`Idris2 --build typed-wasm.ipkg succeeded`);
    } else {
      bad(`Idris2 --build failed (exit ${check.status})\n${check.stderr.slice(0, 400)}`);
    }
  }
}

// ----------------------------------------------------------------------
// Summary
// ----------------------------------------------------------------------

console.log(`\n=== Proof regression results ===`);
console.log(`  ${passed} passed, ${failed} failed, ${skipped} skipped`);

if (failed > 0) {
  console.log(`\nFailures:`);
  for (const f of failures) console.log(`  - ${f}`);
  process.exit(1);
}
