// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 6 — Result-type (access return type known)
//
// L6 attests that every typed-access operation (`region.get`,
// `region.set`, match scrutinee, nested field projection) produces a
// value whose type is known and flowed through downstream use. The
// Idris2 proof layer (`TypedAccess.idr`, `AccessResult` witness) carries
// the full soundness story; the ReScript checker surfaces the narrow
// slice that lives above the type checker — most importantly the
// field-path resolver (`resolveFieldPath` / `resolveFurtherFieldPath`
// in Checker.res) and the striated-region whole-record-pointer ban
// (`isWholeRecordPointer`), which is an L6 invariant in disguise:
// striated layout has no meaningful whole-record type, so the checker
// rejects field declarations that would demand one.
//
// Surface exposure in the checker:
//   - `checkStriatedRegion` (L6 carrier): rejects `ptr<@R>` /
//     `unique<@R>` / `ref<@R>` fields inside a `striated` region —
//     these fields have no contiguous target and therefore no
//     meaningful result type. This is directly testable.
//   - `resolveFieldPath` / `resolveFurtherFieldPath`: match-scrutinee
//     path resolution terminates at the field's declared type; the
//     exhaustiveness check fires ONLY because the result type is
//     known to be a union. An indirect but load-bearing L6 witness.
//   - Nested `pos.x` field access through an embedded region reaches
//     the primitive type — positive clean-check attestation that the
//     path resolver threads through `@R` → primitive.
//
// Run: node tests/levels/L6.mjs

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

console.log("=== Level 6: Result-type (access return type known) ===\n");

// ── Positive: embedded-region field projection reaches primitive ─────
// `region.get $players[idx] .pos.x` walks @Vec2 → f32. The L6 carrier
// is the path resolver; a clean check means the type of the leaf was
// resolvable.

run(
  `region Vec2 {
    x: f32;
    y: f32;
  }
  region Players[32] {
    hp: i32;
    pos: @Vec2;
  }
  fn read_pos_x(players: &region<Players>, idx: i32) -> f32
    effects { ReadRegion(Players), ReadRegion(Vec2) }
  {
    region.get $players[idx] .pos.x -> px;
    return px;
  }`,
  { kind: "clean" },
  "nested @Vec2 → f32 field projection",
);

// ── Negative: striated region with a whole-record pointer field ──────
// `ptr<@Inner>` in a striated region has no contiguous target and
// therefore no coherent result type. checkStriatedRegion flags it.

run(
  `region Inner {
    value: i32;
  }
  region Outer[64] striated {
    ptr_field: ptr<@Inner>;
    v: i32;
  }`,
  { kind: "diagnostic", needles: ["whole-record pointer"] },
  "striated region rejects `ptr<@Inner>` whole-record field",
);

// ── Negative: striated region with `unique<@R>` whole-record ptr ─────

run(
  `region Inner {
    value: i32;
  }
  region Outer[64] striated {
    uniq: unique<@Inner>;
    v: i32;
  }`,
  { kind: "diagnostic", needles: ["whole-record pointer"] },
  "striated region rejects `unique<@Inner>` whole-record field",
);

// ── Positive: striated region with only primitive fields ─────────────
// Primitives have a well-defined per-stripe layout, so result types
// remain known. Clean check.

run(
  `region Particles[512] striated {
    x: f32;
    y: f32;
    hp: i32;
    colour: u32;
  }`,
  { kind: "clean" },
  "striated region with primitive fields only",
);

// ── Positive: match scrutinee resolves to union via embedded path ────
// Path: Enemies.kind → UnionType(...) — exhaustiveness check passes
// because the result type at the leaf is a known union.

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
    };
    hp: i32;
  }
  fn dispatch(e: &region<Enemies>, i: i32) {
    match $e[i] .kind {
      | Minion => { return; }
      | Boss => { return; }
    }
  }`,
  { kind: "clean" },
  "match arm resolution via field path (result type = union)",
);

// ── Negative: match scrutinee resolves to a non-union leaf ───────────
// `$e[i] .hp` — hp is i32, not a union. The checker's result-type
// path (`extractUnionVariants`) returns None, firing the "must be a
// union-typed field" diagnostic.

run(
  `region Enemies[10] {
    kind: union {
      Minion: i32;
      Boss: i32;
    };
    hp: i32;
  }
  fn dispatch(e: &region<Enemies>, i: i32) {
    match $e[i] .hp {
      | Minion => { return; }
    }
  }`,
  { kind: "diagnostic", needles: ["union-typed field"] },
  "match scrutinee with non-union leaf type",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L6: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
