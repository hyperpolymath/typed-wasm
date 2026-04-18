// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// tests/e2e/e2e-driver.mjs — Full-pipeline E2E driver for typed-wasm.
//
// Runs every `.twasm` example through the complete front-end pipeline:
//
//     source -> Lexer -> Parser -> Checker -> diagnostics
//
// The tests/smoke/e2e-smoke.mjs driver exercises one example
// (01-single-module.twasm) and stops at schema extraction. This driver
// covers every example and the checker, which is where v1.1-v1.5 surface
// enforcement actually lives (const literal-only, exhaustive match,
// yield-shape agreement, striated layout, isolated-module boundary,
// session protocol, resource capabilities, choreography composition).
//
// A well-formed example must check with zero diagnostics. An example
// intentionally wired to demonstrate a safety violation must have a
// `// E2E: expect-diagnostic <tag>` pragma on any line; this driver then
// asserts at least one diagnostic mentions `<tag>`.
//
// Run: node tests/e2e/e2e-driver.mjs

import { readFileSync, readdirSync } from "node:fs";
import { resolve, dirname, basename } from "node:path";
import { fileURLToPath } from "node:url";
import { parseModule } from "../../src/parser/Parser.mjs";
import { checkModule } from "../../src/parser/Checker.mjs";

const __dirname = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(__dirname, "../..");
const examplesDir = resolve(projectRoot, "examples");

// ── Pragma extraction ────────────────────────────────────────────────
//
// Accept one of:
//   // E2E: expect-clean           (checker must report zero diagnostics)
//   // E2E: expect-diagnostic foo  (checker must report a diagnostic
//                                   whose message contains "foo")
//   // E2E: skip reason=...        (example targets a level whose grammar
//                                   is not yet in the v1.5 parser; recorded
//                                   but does not count as pass or fail)
//
// Default (no pragma) = expect-clean.

function extractPragmas(source) {
  const pragmas = { kind: "clean", needles: [], skipReason: null };
  for (const line of source.split("\n")) {
    const m = line.match(/\/\/\s*E2E:\s*(\S+)(?:\s+(.+))?/);
    if (!m) continue;
    if (m[1] === "expect-clean") {
      pragmas.kind = "clean";
    } else if (m[1] === "expect-diagnostic") {
      pragmas.kind = "diagnostic";
      if (m[2]) pragmas.needles.push(m[2].trim());
    } else if (m[1] === "skip") {
      pragmas.kind = "skip";
      pragmas.skipReason = m[2] ? m[2].trim() : "(no reason given)";
    }
  }
  return pragmas;
}

// ── Per-example runner ───────────────────────────────────────────────

let passed = 0;
let failed = 0;
let skipped = 0;
const failures = [];

function runExample(filename) {
  const path = resolve(examplesDir, filename);
  const source = readFileSync(path, "utf-8");
  const pragmas = extractPragmas(source);

  if (pragmas.kind === "skip") {
    skipped++;
    console.log(`  SKIP  ${filename} — ${pragmas.skipReason}`);
    return;
  }

  const parseResult = parseModule(source);
  if (parseResult.TAG !== "Ok") {
    failed++;
    failures.push(`${filename}: parse failed — ${parseResult._0.message}`);
    console.log(`  FAIL  ${filename} — parse failed`);
    return;
  }

  const module_ = parseResult._0;
  const diags = checkModule(module_);

  if (pragmas.kind === "clean") {
    if (diags.length === 0) {
      passed++;
      console.log(`  OK    ${filename} (clean, ${module_.declarations.length} decls)`);
    } else {
      failed++;
      const msgs = diags.map(d => d.message).join("; ");
      failures.push(`${filename}: expected clean, got ${diags.length} diagnostic(s): ${msgs}`);
      console.log(`  FAIL  ${filename} — ${diags.length} unexpected diagnostic(s)`);
    }
  } else {
    // expect-diagnostic: at least one diag must mention each needle
    const allMsgs = diags.map(d => d.message).join(" | ");
    const missing = pragmas.needles.filter(n => !allMsgs.includes(n));
    if (missing.length === 0 && diags.length > 0) {
      passed++;
      console.log(`  OK    ${filename} (expected diagnostic, got ${diags.length})`);
    } else {
      failed++;
      failures.push(
        `${filename}: expected diagnostic(s) ${pragmas.needles.join(", ")}, missing ${missing.join(", ")}`,
      );
      console.log(`  FAIL  ${filename} — expected-diagnostic mismatch`);
    }
  }
}

// ── Main ─────────────────────────────────────────────────────────────

console.log("=== typed-wasm E2E driver: parse + check every example ===\n");

const twasmFiles = readdirSync(examplesDir)
  .filter(f => f.endsWith(".twasm"))
  .sort();

if (twasmFiles.length === 0) {
  console.error("No .twasm examples found in examples/");
  process.exit(1);
}

console.log(`Found ${twasmFiles.length} example(s):\n`);

for (const f of twasmFiles) {
  runExample(f);
}

console.log(`\n--- E2E driver: ${passed} passed, ${failed} failed, ${skipped} skipped ---`);

if (failed > 0) {
  console.log("\nFailures:");
  for (const f of failures) {
    console.log(`  - ${f}`);
  }
  process.exit(1);
}

process.exit(0);
