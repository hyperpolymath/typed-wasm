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
//     `idris2 --check src/abi/typed-wasm.ipkg` — actually typechecks the
//     proof package. Catches the case where a theorem name still exists
//     but its body no longer typechecks. This is the strong test; it
//     requires an Idris2 toolchain at the version pinned in
//     src/abi/typed-wasm.ipkg (currently 0.8.0).
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

  // Layout.idr — cross-language layout contracts (aggregate library role)
  ["Layout.idr", /^subTrans\s*:/m, "Subtype transitivity"],
  ["Layout.idr", /^wasmGCEqRefl\s*:/m, "WasmGC structural-equality reflexivity"],

  // Proofs.idr — main theorem suite
  ["Proofs.idr", /^composeCertificates\s*:/m, "Certificate composition"],
  ["Proofs.idr", /^buildCertificate\s*:/m, "Certificate construction"],
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
    console.log(`  Running: ${idris2Path} --check ${ipkg}`);
    const check = spawnSync(idris2Path, ["--check", "typed-wasm.ipkg"], {
      cwd: join(ROOT, "src/abi"),
      encoding: "utf8",
      timeout: 300_000,
    });
    if (check.status === 0) {
      ok(`Idris2 --check typed-wasm.ipkg succeeded`);
    } else {
      bad(`Idris2 --check failed (exit ${check.status})\n${check.stderr.slice(0, 400)}`);
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
