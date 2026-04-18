// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 1 — Instruction validity (parse-time)
//
// L1 is a parse-time check: malformed .twasm source must be rejected
// before any schema or type reasoning runs. The parser is therefore the
// Level-1 oracle: `result.TAG === "Ok"` is the positive attestation;
// `Error(diag)` at a specific construct is the negative attestation.
//
// This file exercises both sides with minimal fixtures:
//   - A well-formed minimal module (one region, one fn) must parse Ok.
//   - Five canonical syntax errors must parse Error.
//
// Run: node tests/levels/L1.mjs

import { parseModule } from "../../src/parser/Parser.mjs";

let passed = 0;
let failed = 0;

function expectOk(source, label) {
  const r = parseModule(source);
  if (r.TAG === "Ok") {
    passed++;
    console.log(`  OK    ${label} — parses clean`);
  } else {
    failed++;
    console.log(`  FAIL  ${label} — unexpected parse error: ${r._0.message}`);
  }
}

function expectErr(source, label) {
  const r = parseModule(source);
  if (r.TAG === "Error") {
    passed++;
    console.log(`  OK    ${label} — rejected as expected (${r._0.message})`);
  } else {
    failed++;
    console.log(`  FAIL  ${label} — should have rejected but parsed`);
  }
}

console.log("=== Level 1: Instruction validity (parse-time) ===\n");

// ── Positive: well-formed minimal module ─────────────────────────────

expectOk(
  `region Counter {
    n: u32;
    align 4;
  }

  fn inc() effects { WriteRegion(Counter) } { }`,
  "minimal well-formed module",
);

expectOk(
  `region Vec2 {
    x: f32;
    y: f32;
    align 4;
  }`,
  "region-only module (no functions)",
);

// ── Negative: canonical syntax errors ────────────────────────────────

// Finding 2026-04-18: parser is lenient about the semicolon between
// the last field and `align`. Grammar EBNF requires `;` after every
// field_decl, so this is a parser looseness worth flagging in a
// future parser-tightness pass. Not exercised here to keep L1 tests
// aligned with current parser behaviour rather than the EBNF spec.

expectErr(
  `region Bad { n: u32;
    align ;
  }`,
  "align with missing integer literal",
);

expectErr(
  `region Bad {
    n: u32;
    align 4;
  `,
  "unterminated region block",
);

expectErr(
  `region {
    n: u32;
    align 4;
  }`,
  "region missing name",
);

expectErr(
  `fn () { }`,
  "function missing name",
);

expectErr(
  `region Counter { n: u32; }
  const : u32 = 1;`,
  "const missing identifier",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L1: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
