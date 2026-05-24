#!/usr/bin/env node
// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Claim-envelope aspect test.
//
// Every claim this repo makes in human-readable docs (README.adoc,
// ROADMAP.adoc, LEVEL-STATUS.md, EXPLAINME.adoc) is also a contract with
// the artefacts it ships (src/abi/typed-wasm.ipkg, src/parser/*, Rust
// crate constants, CI toolchain pins). When docs and artefacts drift,
// nobody notices until an audit week later.
//
// This test catches the drift class directly. Each assertion picks a
// claim made somewhere in the doc estate and checks it against the
// artefact that should embody it. It exits non-zero on any drift.
//
// The 2026-05 deep audit caught five drifts that this test is designed
// to have caught automatically:
//   - "L11/L12 are not in typed-wasm.ipkg" (three doc files said so;
//     the ipkg listed them)
//   - "believe_me: 0" badge but unverified
//   - OWNERSHIP_SECTION_NAME / wire-byte layout vs README spec
//   - Justfile/Justfile/e2e.sh referencing renamed files
//   - CI toolchain pins lagging source-required versions
//
// Run with:  node tests/aspect/claim-envelope.mjs
// Wired into Justfile `test-aspect` and `quality` umbrella.

import { readFileSync, existsSync, readdirSync } from "node:fs";
import { resolve, dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..", "..");

let passed = 0;
let failed = 0;
let skipped = 0;
const failures = [];

function ok(msg) { console.log(`  OK    ${msg}`); passed++; }
function bad(msg) { console.log(`  FAIL  ${msg}`); failed++; failures.push(msg); }
function skip(msg) { console.log(`  SKIP  ${msg}`); skipped++; }
function section(name) { console.log(`\n=== ${name} ===`); }

function read(rel) {
  return readFileSync(join(ROOT, rel), "utf8");
}

// ----------------------------------------------------------------------
// 1. ipkg membership ⇔ documentation
// ----------------------------------------------------------------------
section("1. ipkg membership matches doc claims");

const ipkg = read("src/abi/typed-wasm.ipkg");
const ipkgModules = ipkg
  .split("\n")
  .map((l) => l.replace(/^[\s,]+/, "").trim())
  .filter((l) => /^[A-Z][A-Za-z0-9_.]+$/.test(l));

if (ipkgModules.length === 0) {
  bad("could not parse any modules out of typed-wasm.ipkg");
} else {
  ok(`typed-wasm.ipkg lists ${ipkgModules.length} modules`);
}

// Specific claim: L11/L12 (Tropical, Epistemic) status across docs vs ipkg.
// Audit fallout 2026-05: three doc files said "L11/L12 not in ipkg" when
// they were. We assert the docs match the actual ipkg state.
const tropicalInPkg = ipkgModules.includes("TypedWasm.ABI.Tropical");
const epistemicInPkg = ipkgModules.includes("TypedWasm.ABI.Epistemic");

if (tropicalInPkg) {
  ok("Tropical (L11) is in typed-wasm.ipkg");
} else {
  bad("Tropical (L11) missing from typed-wasm.ipkg");
}
if (epistemicInPkg) {
  ok("Epistemic (L12) is in typed-wasm.ipkg");
} else {
  bad("Epistemic (L12) missing from typed-wasm.ipkg");
}

// Now the contrapositive: if L11/L12 are in-package, no doc may claim
// "not part of the default checked Idris2 package" or similar without
// being marked superseded.
function assertDocsAgreeOnL11L12(path, regex) {
  if (!existsSync(join(ROOT, path))) {
    skip(`${path} not found — cannot cross-check L11/L12 claim`);
    return;
  }
  const text = read(path);
  const m = text.match(regex);
  if (m && (tropicalInPkg || epistemicInPkg)) {
    bad(
      `${path}: still claims "${m[0].slice(0, 60).replace(/\s+/g, " ")}..." ` +
        `while L11/L12 are in the ipkg`,
    );
  } else {
    ok(`${path} L11/L12 claims do not contradict the ipkg`);
  }
}

// Pattern that matches the dangerous stale wording. Designed conservatively
// to false-positive only on the exact "not in package / not part of ipkg"
// stale phrasing.
const stalePattern =
  /L11.{0,4}L12[^\n]{0,180}?(not part of|not in.*(?:package|ipkg)|standalone.*fail)/i;
assertDocsAgreeOnL11L12("ROADMAP.adoc", stalePattern);
assertDocsAgreeOnL11L12("LEVEL-STATUS.md", stalePattern);
assertDocsAgreeOnL11L12("README.adoc", stalePattern);

// ----------------------------------------------------------------------
// 2. believe_me / postulate / assert_total badge
// ----------------------------------------------------------------------
section("2. unsound-pattern badge truthfulness");

const idrisFiles = [];
function collectIdris(dir) {
  for (const entry of readdirSync(join(ROOT, dir), { withFileTypes: true })) {
    const sub = `${dir}/${entry.name}`;
    if (entry.isDirectory()) collectIdris(sub);
    else if (entry.name.endsWith(".idr")) idrisFiles.push(sub);
  }
}
collectIdris("src/abi");

const banned = /\b(believe_me|postulate|assert_total|really_believe_me|Admitted|sorry|prim__crash|idris_crash)\b/;
let badPatternHits = 0;
for (const f of idrisFiles) {
  const lines = read(f).split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    // Skip comment lines (-- ...) and block-comment-like (| header)
    if (/^\s*(--|\|\|\|)/.test(line)) continue;
    if (banned.test(line)) {
      bad(`${f}:${i + 1} has banned pattern: ${line.trim()}`);
      badPatternHits++;
    }
  }
}
if (badPatternHits === 0) {
  ok(`all ${idrisFiles.length} .idr files: 0 non-comment occurrences of banned patterns`);
}

// Now cross-check that the README badge actually says 0.
const readme = read("README.adoc");
if (/believe__me-0/.test(readme)) {
  ok("README badge claims believe_me=0 (matches reality)");
} else if (/believe__me-[0-9]+/.test(readme)) {
  bad("README badge no longer claims believe_me=0 — does it still match reality?");
} else {
  skip("README has no believe_me badge to cross-check");
}

// ----------------------------------------------------------------------
// 3. Wire format: OwnershipKind enum matches README spec
// ----------------------------------------------------------------------
section("3. Rust crate constants match README spec");

const libRs = read("crates/typed-wasm-verify/src/lib.rs");

// Spec from crates/typed-wasm-verify/README.md:
//   u8 param_kinds  (0=Unrestricted, 1=Linear, 2=SharedBorrow, 3=ExclBorrow)
const expectedWire = [
  ["Unrestricted", 0],
  ["Linear", 1],
  ["SharedBorrow", 2],
  ["ExclBorrow", 3],
];
for (const [name, byte] of expectedWire) {
  const re = new RegExp(`${name}\\s*=\\s*${byte}\\b`);
  if (re.test(libRs)) {
    ok(`OwnershipKind::${name} = ${byte} (matches README spec)`);
  } else {
    bad(`OwnershipKind::${name} = ${byte} not found in lib.rs`);
  }
}

// Section name constant
if (/OWNERSHIP_SECTION_NAME:\s*&str\s*=\s*"affinescript\.ownership"/.test(libRs)) {
  ok("OWNERSHIP_SECTION_NAME = \"affinescript.ownership\" (matches doc claims)");
} else {
  bad("OWNERSHIP_SECTION_NAME constant drifted from \"affinescript.ownership\"");
}

// ----------------------------------------------------------------------
// 4. Test-file paths referenced from CI / Justfile actually exist
// ----------------------------------------------------------------------
section("4. CI + Justfile path references are real");

function assertReferencedPathsExist(file, regex, label) {
  if (!existsSync(join(ROOT, file))) {
    skip(`${file} not found — cannot scan for ${label}`);
    return;
  }
  const text = read(file);
  let m;
  const seen = new Set();
  while ((m = regex.exec(text)) !== null) {
    const path = m[1];
    if (seen.has(path)) continue;
    seen.add(path);
    if (existsSync(join(ROOT, path))) {
      ok(`${file} -> ${path}`);
    } else {
      bad(`${file} references ${path} which does not exist`);
    }
  }
}

// Justfile recipe bodies: capture `node tests/...mjs` and `bash tests/...sh`.
assertReferencedPathsExist(
  "Justfile",
  /(?:node|bash)\s+(tests\/[^\s]+\.(?:mjs|sh)|benchmarks\/[^\s]+\.mjs)/g,
  "Justfile invoked test/bench files",
);

// tests/e2e.sh referenced paths (the file-existence check arrays).
assertReferencedPathsExist(
  "tests/e2e.sh",
  /"(tests\/[^"]+\.mjs|[A-Z][^"\s]+\.(?:adoc|md))"/g,
  "tests/e2e.sh referenced files",
);

// ----------------------------------------------------------------------
// 5. CI toolchain pins match what the source actually requires
// ----------------------------------------------------------------------
section("5. CI toolchain pins match source intent");

const e2eYml = existsSync(join(ROOT, ".github/workflows/e2e.yml"))
  ? read(".github/workflows/e2e.yml")
  : "";
const buildZig = existsSync(join(ROOT, "ffi/zig/build.zig"))
  ? read("ffi/zig/build.zig")
  : "";
const proofsIdr = existsSync(join(ROOT, "src/abi/TypedWasm/ABI/Proofs.idr"))
  ? read("src/abi/TypedWasm/ABI/Proofs.idr")
  : "";

// Zig: source intent comes from build.zig header comment.
// CI pin lives in e2e.yml as `ZIG_VERSION="x.y.z"`.
const zigSrcWantMatch = buildZig.match(/Zig\s+(\d+\.\d+)/);
const zigCiMatch = e2eYml.match(/ZIG_VERSION="(\d+)\.(\d+)\.\d+"/);
if (zigSrcWantMatch && zigCiMatch) {
  const wantMajorMinor = zigSrcWantMatch[1];
  const haveMajorMinor = `${zigCiMatch[1]}.${zigCiMatch[2]}`;
  // build.zig says "0.15+", so CI's major.minor must be >= source intent.
  const [wantMaj, wantMin] = wantMajorMinor.split(".").map(Number);
  const [haveMaj, haveMin] = haveMajorMinor.split(".").map(Number);
  if (haveMaj > wantMaj || (haveMaj === wantMaj && haveMin >= wantMin)) {
    ok(`Zig CI pin ${haveMajorMinor}.x >= build.zig requirement ${wantMajorMinor}+`);
  } else {
    bad(`Zig CI pin ${haveMajorMinor}.x < build.zig requirement ${wantMajorMinor}+`);
  }
} else {
  skip("could not extract both Zig source intent and CI pin");
}

// Idris2: source intent comes from Proofs.idr header comment.
const idrisSrcWantMatch = proofsIdr.match(/Idris2\s+(\d+\.\d+\.\d+)/);
const idrisCiMatch = e2eYml.match(/IDRIS2_VERSION="(\d+\.\d+\.\d+)"/);
if (idrisSrcWantMatch && idrisCiMatch) {
  if (idrisSrcWantMatch[1] === idrisCiMatch[1]) {
    ok(`Idris2 CI pin ${idrisCiMatch[1]} matches Proofs.idr "${idrisSrcWantMatch[1]}"`);
  } else {
    bad(`Idris2 CI pin ${idrisCiMatch[1]} != Proofs.idr "verified with ${idrisSrcWantMatch[1]}"`);
  }
} else {
  skip("could not extract both Idris2 source intent and CI pin");
}

// ----------------------------------------------------------------------
// 6. Example corpus parses (or is documented skipped)
// ----------------------------------------------------------------------
section("6. .twasm example corpus is exercised");

const exampleDir = "examples";
const examples = existsSync(join(ROOT, exampleDir))
  ? readdirSync(join(ROOT, exampleDir)).filter((f) => f.endsWith(".twasm"))
  : [];
if (examples.length === 0) {
  bad("examples/*.twasm corpus is empty");
} else {
  ok(`${examples.length} .twasm examples present`);
  // The e2e driver tests these; we only verify presence here so the
  // aspect test stays decoupled from parser availability.
}

// ----------------------------------------------------------------------
// 7. RSR / surface files claimed by docs actually exist
// ----------------------------------------------------------------------
section("7. RSR surface files exist");

const rsrFiles = [
  "README.adoc",
  "EXPLAINME.adoc",
  "SECURITY.md",
  "CONTRIBUTING.md",
  "LICENSE",
  "Justfile",
  "0-AI-MANIFEST.a2ml",
  "LEVEL-STATUS.md",
  "ROADMAP.adoc",
  "PROOF-NEEDS.md",
  "TEST-NEEDS.md",
];
for (const f of rsrFiles) {
  if (existsSync(join(ROOT, f))) ok(`RSR file: ${f}`);
  else bad(`RSR file missing: ${f}`);
}

// ----------------------------------------------------------------------
// 8. Path references in docs resolve to real files
//
// Catches the rename-drift class: a file gets renamed but doc references
// keep pointing at the old path. Caught by Phase 0 housekeeping that
// found 5 stale references to spec/10-levels-for-wasm.adoc after it
// became spec/type-safety-levels-for-wasm.adoc.
//
// We scan README.adoc, ROADMAP.adoc, EXPLAINME.adoc, and CLAUDE.md for
// repo-relative path-ish tokens matching common source-file extensions
// and verify each resolves on disk.
// ----------------------------------------------------------------------
section("8. Path references in docs resolve to real files");

function maybeRead(rel) {
  try { return readFileSync(join(ROOT, rel), "utf8"); } catch { return null; }
}

const docsToScan = [
  "README.adoc",
  "ROADMAP.adoc",
  "EXPLAINME.adoc",
  ".claude/CLAUDE.md",
];

const PATH_LIKE = /(?<![A-Za-z0-9_./-])([a-z0-9][a-z0-9._/-]*\.(?:adoc|md|mjs|res|idr|zig|rs|ebnf|toml|ipkg))(?![A-Za-z0-9_./-])/gi;

const ALLOWLIST_FRAGMENTS = [
  "rsr-template-repo",
  "github.com",
  "node_modules/",
  "{{",
  "example.com",
  "/home/runner/",
  // Cross-repo references (different repos in the hyperpolymath ecosystem)
  "typedqliser/",
  "affinescript/",
  "ephapax/",
  "hypatia/",
  "standards/",
  "typell/",
  "vql-ut/",
  "echidna/",
];

// Skip bare filenames without a directory part — those are conventional
// references in prose (e.g. "see PROOF-NEEDS.md") that may live anywhere
// in the tree. Only check refs with at least one `/` (an actual path).
function isFullPath(ref) {
  return ref.includes("/");
}

let docPathRefsChecked = 0;
const missingRefs = [];

for (const doc of docsToScan) {
  const content = maybeRead(doc);
  if (content === null) {
    skip(`${doc}: doc absent — cannot scan`);
    continue;
  }
  const seen = new Set();
  for (const match of content.matchAll(PATH_LIKE)) {
    const ref = match[1];
    if (seen.has(ref)) continue;
    seen.add(ref);
    if (ALLOWLIST_FRAGMENTS.some((f) => ref.includes(f))) continue;
    if (ref.includes("*") || ref.includes("?")) continue;
    if (!isFullPath(ref)) continue; // bare filenames are prose conventions
    docPathRefsChecked++;
    if (!existsSync(join(ROOT, ref))) {
      missingRefs.push(`${doc}: ${ref}`);
    }
  }
}

// Print full list inline so reviewers see each failure, not just first-5.
if (missingRefs.length === 0) {
  ok(`All ${docPathRefsChecked} path references across ${docsToScan.length} docs resolve on disk`);
} else {
  bad(`${missingRefs.length} of ${docPathRefsChecked} doc path references are stale:`);
  for (const r of missingRefs) console.log(`    - ${r}`);
}

// ----------------------------------------------------------------------
// Summary
// ----------------------------------------------------------------------
console.log("");
console.log("==============================");
console.log(` Aspect (claim envelope): ${passed} passed, ${failed} failed, ${skipped} skipped`);
console.log("==============================");
if (failed > 0) {
  console.log("\nClaim-envelope drift detected:");
  for (const f of failures) console.log(`  - ${f}`);
  process.exit(1);
}
process.exit(0);
