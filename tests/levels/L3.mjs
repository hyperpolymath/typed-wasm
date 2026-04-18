// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 3 — Type-compatible access
//
// L3 attests that every field read or union-variant deref matches the
// declared field type. The ReScript checker surfaces this at two sites:
//
//   a) `match` arms must exactly cover the declared union variants; an
//      arm tag that names a variant not in the union is a type-level
//      error the checker flags as "unknown arm tag".
//   b) A `const` initializer's value must have the same primitive shape
//      as the declared `constType` (v1.1 surface rule,
//      Checker.constValueIsLiteral + type-match).
//
// Run: node tests/levels/L3.mjs

import { parseModule } from "../../src/parser/Parser.mjs";
import { checkModule } from "../../src/parser/Checker.mjs";

let passed = 0;
let failed = 0;

function run(source, expect, label) {
  const pr = parseModule(source);
  if (pr.TAG !== "Ok") {
    failed++;
    console.log(`  FAIL  ${label} — parse error: ${pr._0.message}`);
    return;
  }
  const diags = checkModule(pr._0);
  if (expect.kind === "clean") {
    if (diags.length === 0) {
      passed++;
      console.log(`  OK    ${label} — clean check`);
    } else {
      failed++;
      const msgs = diags.map(d => d.message).join("; ");
      console.log(`  FAIL  ${label} — expected clean, got ${diags.length}: ${msgs}`);
    }
  } else {
    const allMsgs = diags.map(d => d.message).join(" | ");
    const missing = expect.needles.filter(n => !allMsgs.includes(n));
    if (missing.length === 0 && diags.length > 0) {
      passed++;
      console.log(`  OK    ${label} — diagnostic fired as expected`);
    } else {
      failed++;
      console.log(`  FAIL  ${label} — expected needles ${expect.needles.join(", ")}, got "${allMsgs}"`);
    }
  }
}

console.log("=== Level 3: Type-compatible access ===\n");

// ── Positive: exhaustive match over all variants ─────────────────────

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
    };
  }
  fn dispatch(e: &region<Enemies>, i: i32) {
    match $e[i] .kind {
      | Minion => { return; }
      | Boss => { return; }
    }
  }`,
  { kind: "clean" },
  "exhaustive match over union variants",
);

// ── Negative: match arm names a variant that does not exist ──────────

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
    };
  }
  fn dispatch(e: &region<Enemies>, i: i32) {
    match $e[i] .kind {
      | Minion => { return; }
      | Boss => { return; }
      | GhostVariant => { return; }
    }
  }`,
  { kind: "diagnostic", needles: ["GhostVariant"] },
  "match arm names unknown variant",
);

// ── Negative: match misses a variant (non-exhaustive) ────────────────

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
      Shade: i32;
    };
  }
  fn dispatch(e: &region<Enemies>, i: i32) {
    match $e[i] .kind {
      | Minion => { return; }
      | Boss => { return; }
    }
  }`,
  { kind: "diagnostic", needles: ["Shade"] },
  "non-exhaustive match missing variant",
);

// ── Negative: duplicate match arm ────────────────────────────────────

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
    };
  }
  fn dispatch(e: &region<Enemies>, i: i32) {
    match $e[i] .kind {
      | Minion => { return; }
      | Minion => { return; }
      | Boss => { return; }
    }
  }`,
  { kind: "diagnostic", needles: ["duplicate"] },
  "duplicate match arm",
);

// ── Positive: const with matching literal type ───────────────────────

run(
  `const max_hp : i32 = 100;`,
  { kind: "clean" },
  "const i32 = int literal",
);

// ── Negative: const with non-literal initializer ─────────────────────

run(
  `const max_hp : i32 = 100 + 1;`,
  { kind: "diagnostic", needles: ["literal"] },
  "const with non-literal expression",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L3: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
