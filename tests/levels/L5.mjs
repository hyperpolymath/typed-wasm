// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 5 — Bounds-proof (compile-time offset verification)
//
// L5 attests that every indexed access `$r[i]` is provably within the
// region's declared instance count at the point of use. The Idris2
// proof layer carries this as `InBounds` witnesses in
// `src/abi/TypedWasm/ABI/TypedAccess.idr` and `Levels.idr`; the ReScript
// parser admits indexed field paths whose index is any expression, and
// the checker resolves the field path but does NOT perform constant
// propagation or interval analysis at v1.1.
//
// Surface exposure in the checker:
//   - The match-statement path walker (`resolveFieldPath` / `walkExpr`)
//     descends through `IndexAccess(expr)` segments as array strips,
//     so a syntactically valid indexed scrutinee `$r[i]` resolves to
//     the element type and the exhaustiveness check runs normally.
//   - No "index out of range" diagnostic exists in Checker.res today;
//     writing a test that asserts one would give false confidence.
//
// What IS testable at this layer, and what this file covers:
//   - Indexed field path through a region with an `instanceCount` parses
//     + checks clean (positive attestation of surfaceable L5 shape).
//   - Field-level `where` constraints (range-predicate clauses like
//     `where 0 <= hp <= 9999`) are parsed as `constraintExpr` entries
//     and the checker threads through them without diagnostics — the
//     bounds proof is Idris2-side but the carrier must survive.
//   - Indexing a striated (SoA) region's projection-only access parses
//     + checks clean, which is the L5 path the L17 "Layout-proof
//     striation" work eventually removes the restriction for.
//
// The "real" L5 enforcement — that an index is provably within
// `instanceCount` — is Idris2-side. This file's role is to certify
// that the ReScript surface accepts the carrier shape without false
// positives.
//
// Run: node tests/levels/L5.mjs

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

console.log("=== Level 5: Bounds-proof (compile-time offset verification) ===\n");

// ── Positive: indexed field access via match scrutinee ───────────────
// The scrutinee `$e[i] .kind` carries one IndexAccess segment; the
// checker's field-path resolver strips the array layer and lands on
// the union type. L5 surface shape round-trips clean.

run(
  `region Enemies[16] {
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
  "indexed region scrutinee `$e[i] .kind` — path resolves",
);

// ── Positive: field-level range constraint carries through checker ───

run(
  `region Players[100] {
    hp: i32;
    max_hp: i32;

    where 0 <= hp <= 9999;
  }`,
  { kind: "clean" },
  "region with field-level `where 0 <= hp <= 9999` constraint",
);

// ── Positive: striated region projection-only indexed access ─────────
// A striated region bans whole-record pointers but primitive field
// projection via an indexed handle is the supported L5 path.

run(
  `region Particles[1024] striated {
    x: f32;
    y: f32;
    vx: f32;
    vy: f32;
  }
  fn step(particles: &mut region<Particles>, i: i32)
    effects { ReadRegion(Particles), WriteRegion(Particles) }
  {
    region.get $particles[i] .x -> px;
    region.set $particles[i] .x, px;
  }`,
  { kind: "clean" },
  "striated region indexed projection access",
);

// ── Positive: fixed-size inline array field `u8[24]` parses clean ────
// Not L5 on its own — but the array-sized field type is the same
// bounded-access carrier the Idris2 layer reasons over.

run(
  `region Labels[8] {
    name: u8[24];
    id: i32;
  }`,
  { kind: "clean" },
  "fixed-size inline array field `u8[24]`",
);

// ── Positive: constant-literal index expression ──────────────────────
// `$players[0]` — a literal index. Parser accepts any expr here; the
// Idris2 InBounds witness is what discharges the proof obligation.

run(
  `region Players[10] {
    hp: i32;
  }
  fn read_first(players: &region<Players>) -> i32
    effects { ReadRegion(Players) }
  {
    region.get $players[0] .hp -> hp;
    return hp;
  }`,
  { kind: "clean" },
  "literal-index access `$players[0]`",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L5: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
