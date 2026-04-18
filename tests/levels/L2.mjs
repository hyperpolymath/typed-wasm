// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 2 — Region-binding (schema lookup)
//
// L2 attests that every declared region has a resolvable schema and
// that the checker surfaces structural lookups before type reasoning
// runs. The positive attestation is "parse + check clean with the
// region present"; the negative attestation is "checker complains
// about a region-targeting construct whose name is undeclared".
//
// Surface exposure: the most direct L2 trigger in the ReScript checker
// is a `match` statement whose target references a field of an
// undeclared region (walkExpr threads the region environment; the
// match arm resolver bottoms out in a "unknown region"-shaped
// diagnostic). A second trigger is a session `transition consume X`
// against a region name not declared anywhere in the module.
//
// Run: node tests/levels/L2.mjs

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

console.log("=== Level 2: Region-binding (schema lookup) ===\n");

// ── Positive: region present, match resolves cleanly ─────────────────

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
  "match against declared region — clean",
);

// ── Negative: match targets a region that is not declared ────────────
//
// Observation: Checker's match resolution walks the function parameter
// list to find the region binding. Passing a parameter whose declared
// region name is absent from the module is the structural L2 failure.

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
    };
  }
  fn dispatch(e: &region<NotDeclared>, i: i32) {
    match $e[i] .kind {
      | Minion => { return; }
      | Boss => { return; }
    }
  }`,
  { kind: "diagnostic", needles: ["unknown region"] },
  "match target names undeclared region",
);

// ── Positive: session referencing declared region-typed state ────────

run(
  `region Players[8] { hp: u32; }
  session OrderFlow {
    state Idle    : i32;
    state Pending : i64;
    transition submit : consume Idle -> yield Pending;
  }`,
  { kind: "clean" },
  "session with primitive-typed states alongside a region",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L2: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
