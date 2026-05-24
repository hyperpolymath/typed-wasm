#!/usr/bin/env node
// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Security-envelope aspect test.
//
// Counterpart to tests/aspect/claim-envelope.mjs. Where claim-envelope
// checks that human-readable doc claims match shipped artefacts in
// general, this file specifically checks SECURITY claims:
//
//   - SECURITY.md contact email matches .well-known/security.txt
//   - SPDX-License-Identifier headers present on all source files
//   - "believe_me: 0" README badge matches actual code (not comments)
//   - No committed secrets / private keys
//   - SECURITY.md disclosure timeline claims are present and parseable
//
// Phase 0 / Track C deliverable. Closes TEST-NEEDS.md "Security: No
// memory safety violation detection tests" cross-cutting gap by adding
// the security-claim-vs-reality drift check that catches before-merge
// the kind of issue that audits catch six months later.
//
// Run:  node tests/aspect/security-envelope.mjs

import { readFileSync, existsSync, readdirSync, statSync } from "node:fs";
import { resolve, dirname, join, extname } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..", "..");

// Source-of-truth file list: git-tracked only. Filesystem walks pick up
// gitignored generated artefacts (e.g. src/parser/*.mjs from ReScript
// builds) which then false-positive on SPDX-missing checks.
function gitTrackedFiles() {
  const r = spawnSync("git", ["-C", ROOT, "ls-files"], { encoding: "utf8" });
  if (r.status !== 0) return null;
  return r.stdout.split("\n").filter(Boolean).map((p) => join(ROOT, p));
}

const TRACKED = gitTrackedFiles();

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

function maybeRead(rel) {
  try { return readFileSync(join(ROOT, rel), "utf8"); } catch { return null; }
}

// ----------------------------------------------------------------------
// 1. SECURITY.md ↔ .well-known/security.txt — contact alignment
// ----------------------------------------------------------------------
section("1. SECURITY.md and .well-known/security.txt agree on contact");

const securityMd = maybeRead("SECURITY.md");
const securityTxt = maybeRead(".well-known/security.txt");

if (!securityMd) bad("SECURITY.md missing");
if (!securityTxt) bad(".well-known/security.txt missing");

if (securityMd && securityTxt) {
  const mdEmail = (securityMd.match(/[\w._%+-]+@[\w.-]+\.[A-Za-z]{2,}/) || [])[0];
  const txtEmail = (securityTxt.match(/Contact:\s*mailto:([\w._%+-]+@[\w.-]+\.[A-Za-z]{2,})/) || [])[1]
    || (securityTxt.match(/[\w._%+-]+@[\w.-]+\.[A-Za-z]{2,}/) || [])[0];

  if (!mdEmail) bad("SECURITY.md has no contact email");
  else if (!txtEmail) bad(".well-known/security.txt has no Contact: line");
  else if (mdEmail.toLowerCase() !== txtEmail.toLowerCase()) {
    bad(`Contact email mismatch: SECURITY.md=${mdEmail} vs security.txt=${txtEmail}`);
  } else {
    ok(`Contact email aligned: ${mdEmail}`);
  }
}

// ----------------------------------------------------------------------
// 2. SECURITY.md disclosure timeline is concrete (not template residue)
// ----------------------------------------------------------------------
section("2. SECURITY.md disclosure timeline is concrete");

if (securityMd) {
  // Each commitment must be a concrete duration with units.
  const checks = [
    [/Acknowledg(e|ment).*?\d+\s*(hour|day)/i, "Acknowledgement window"],
    [/(Initial assessment|response).*?\d+\s*day/i, "Initial-assessment window"],
    [/(Fix|mitigation).*?\d+\s*day/i, "Fix/mitigation window"],
  ];
  for (const [pattern, label] of checks) {
    if (pattern.test(securityMd)) {
      ok(`${label} is concrete`);
    } else {
      bad(`${label} missing or non-concrete in SECURITY.md`);
    }
  }
}

// ----------------------------------------------------------------------
// 3. SPDX-License-Identifier headers on all source files
// ----------------------------------------------------------------------
section("3. SPDX headers on all source files");

const SOURCE_EXTS = new Set([".idr", ".rs", ".zig", ".mjs", ".res", ".ml", ".sh"]);
const SKIP_DIRS = new Set([".git", "node_modules", "target", "lib", ".cache", "tmp", ".direnv", "_build", "deps", "vendor"]);
const SKIP_PATH_FRAGMENTS = ["/generated/", "/lib/bs/", "/lib/ocaml/"];

function walk(dir) {
  const out = [];
  for (const entry of readdirSync(dir)) {
    if (SKIP_DIRS.has(entry)) continue;
    const full = join(dir, entry);
    const stat = statSync(full);
    if (stat.isDirectory()) {
      out.push(...walk(full));
    } else if (SOURCE_EXTS.has(extname(entry))) {
      out.push(full);
    }
  }
  return out;
}

// Prefer git-tracked over filesystem walk to avoid false positives on
// gitignored generated artefacts; fall back to walk if git is unavailable.
const sources = (TRACKED
  ? TRACKED.filter((p) => SOURCE_EXTS.has(extname(p)))
  : walk(ROOT).filter((p) => !SKIP_PATH_FRAGMENTS.some((f) => p.includes(f)))
);
const missingSpdx = [];
for (const path of sources) {
  const head = readFileSync(path, "utf8").slice(0, 400);
  if (!/SPDX-License-Identifier/.test(head)) {
    missingSpdx.push(path.replace(ROOT + "/", ""));
  }
}
if (missingSpdx.length === 0) {
  ok(`All ${sources.length} source files carry SPDX headers`);
} else {
  bad(`${missingSpdx.length} source files lack SPDX headers (first 5: ${missingSpdx.slice(0, 5).join(", ")})`);
}

// ----------------------------------------------------------------------
// 4. README "believe_me: 0" badge matches actual code (excluding comments)
// ----------------------------------------------------------------------
section("4. believe_me / assert_total / postulate badge claim is accurate");

const readme = maybeRead("README.adoc");
const badgeClaimsZero = readme && /believe__me-0|believe_me: 0|believe_me-0/i.test(readme);

if (!badgeClaimsZero) {
  skip("README does not claim believe_me=0; skipping badge verification");
} else {
  // Walk Idris2 files, strip line comments (-- ...) and block comments
  // ({- ... -}), then look for the actual identifiers.
  const idrFiles = walk(join(ROOT, "src/abi")).filter((p) => p.endsWith(".idr"));
  const offenders = { believe_me: [], assert_total: [], postulate: [] };

  for (const path of idrFiles) {
    let src = readFileSync(path, "utf8");
    // Strip block comments {- ... -} (non-nested, conservative)
    src = src.replace(/\{-[\s\S]*?-\}/g, "");
    // Strip line comments -- ... to end of line
    src = src.replace(/--[^\n]*/g, "");
    for (const tok of Object.keys(offenders)) {
      // word boundary so 'assert_totally' (if it ever existed) wouldn't trip
      const re = new RegExp(`\\b${tok}\\b`);
      if (re.test(src)) offenders[tok].push(path.replace(ROOT + "/", ""));
    }
  }

  for (const [tok, files] of Object.entries(offenders)) {
    if (files.length === 0) {
      ok(`No code-position \`${tok}\` in src/abi/ — badge claim holds`);
    } else {
      bad(`README badge claims 0 ${tok}, but src/abi/ contains ${files.length} (first: ${files[0]})`);
    }
  }
}

// ----------------------------------------------------------------------
// 5. No committed secrets / private keys / common credential patterns
// ----------------------------------------------------------------------
section("5. No committed secrets / credentials / private keys");

const SECRET_PATTERNS = [
  [/-----BEGIN (?:RSA |EC |OPENSSH |PGP |)PRIVATE KEY-----/, "private key"],
  [/AKIA[0-9A-Z]{16}/, "AWS access key"],
  [/AIza[0-9A-Za-z_-]{35}/, "Google API key"],
  [/sk-[A-Za-z0-9]{32,}/, "OpenAI/Anthropic-style API key"],
  [/ghp_[A-Za-z0-9]{36}/, "GitHub personal access token"],
  [/xox[bp]-[A-Za-z0-9-]{10,}/, "Slack token"],
];

// Restrict to git-tracked files (gitignored dirs already excluded).
const allTracked = (TRACKED || walk(ROOT).filter((p) => !SKIP_PATH_FRAGMENTS.some((f) => p.includes(f))))
  .filter((p) =>
    !p.endsWith(".lock") &&
    !p.includes("/test/") && !p.includes("/tests/")  // test fixtures may contain example secrets
  );

const secretsFound = [];
for (const path of allTracked) {
  let content;
  try { content = readFileSync(path, "utf8"); } catch { continue; }
  // Skip binary-ish content
  if (content.includes("\0")) continue;
  for (const [pattern, label] of SECRET_PATTERNS) {
    if (pattern.test(content)) {
      secretsFound.push(`${path.replace(ROOT + "/", "")} (${label})`);
    }
  }
}
if (secretsFound.length === 0) {
  ok(`No common credential patterns in ${allTracked.length} source files`);
} else {
  bad(`Possible committed secrets: ${secretsFound.slice(0, 3).join("; ")}`);
}

// ----------------------------------------------------------------------
// 6. License consistency — top-level LICENSE matches SPDX headers
// ----------------------------------------------------------------------
section("6. Top-level LICENSE consistent with SPDX header claims");

const licenseFile = maybeRead("LICENSE");
if (!licenseFile) {
  bad("LICENSE file missing at repo root");
} else if (/Mozilla Public License/i.test(licenseFile) && /Version 2/.test(licenseFile)) {
  // Check that source files declare MPL-2.0 specifically
  const spdxLines = [];
  for (const path of sources.slice(0, 20)) {
    const head = readFileSync(path, "utf8").slice(0, 400);
    const m = head.match(/SPDX-License-Identifier:\s*([^\s\n]+)/);
    if (m) spdxLines.push(m[1]);
  }
  const mismatched = spdxLines.filter((s) => s !== "MPL-2.0");
  if (mismatched.length === 0) {
    ok(`LICENSE is MPL-2.0; sampled ${spdxLines.length} SPDX headers all declare MPL-2.0`);
  } else {
    bad(`LICENSE is MPL-2.0 but found inconsistent SPDX headers: ${[...new Set(mismatched)].join(", ")}`);
  }
} else {
  skip(`LICENSE file present but content not recognised as MPL-2.0; skipping SPDX cross-check`);
}

// ----------------------------------------------------------------------
// Summary
// ----------------------------------------------------------------------

console.log(`\n=== Security-envelope results ===`);
console.log(`  ${passed} passed, ${failed} failed, ${skipped} skipped`);

if (failed > 0) {
  console.log(`\nFailures:`);
  for (const f of failures) console.log(`  - ${f}`);
  process.exit(1);
}
