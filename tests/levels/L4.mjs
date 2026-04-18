// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 4 — Null safety (opt<T> tracking)
//
// L4 enforces that nullable pointers (`opt<T>`, `opt<@R>`, `opt<ptr<T>>`)
// are distinct from non-nullable forms in the type system: a function
// taking `&region<X>` receives a witness that the handle is non-null,
// while `opt<...>` fields in a region force an explicit `is_null` check
// before use.
//
// Surface exposure in the ReScript checker: L4 is almost entirely
// structural. The AST distinguishes `OptionalType(...)` from bare
// `PointerType(...)` / `RegionRef(...)` at parse time; no ReScript
// diagnostic fires on a "forgot to null-check" pattern today (that
// analysis lives in the Idris2 `Pointer.idr` / `Levels.idr` Ptr-NonNull
// witness). What IS testable at this layer is:
//
//   - `opt<T>` fields parse + check clean (positive: nullability is a
//     first-class type constructor).
//   - `&region<X>` and `&mut region<X>` parameter syntax parses + checks
//     clean (positive: non-null handle types are well-formed).
//   - Nested nullable forms — `opt<ptr<T>>`, `opt<@R>` — round-trip
//     through parser + checker without diagnostics.
//   - `is_null(...)` as a predicate expression threads through the
//     checker without firing.
//
// The L4 "proven enforcement" — that a read through a non-null handle
// never dereferences null — lives in the Idris2 proof layer
// (src/abi/TypedWasm/ABI/Pointer.idr and Levels.idr, Ptr-NonNull
// witness). This file's role is to prove the ReScript surface accepts
// all well-formed L4 shapes without false positives.
//
// Run: node tests/levels/L4.mjs

import { parseModule } from "../../src/parser/Parser.mjs";
import { checkModule } from "../../src/parser/Checker.mjs";

let passed = 0;
let failed = 0;

function run(source, expect, label) {
  const pr = parseModule(source);
  if (pr.TAG !== "Ok") {
    if (expect.kind === "parseErr") {
      passed++;
      console.log(`  OK    ${label} — parse rejected as expected`);
      return;
    }
    failed++;
    console.log(`  FAIL  ${label} — parse error: ${pr._0.message}`);
    return;
  }
  if (expect.kind === "parseErr") {
    failed++;
    console.log(`  FAIL  ${label} — should have failed to parse`);
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

console.log("=== Level 4: Null safety (opt<T> tracking) ===\n");

// ── Positive: opt<@R> field round-trips parser + checker clean ───────

run(
  `region Vec2 {
    x: f32;
    y: f32;
  }
  region Enemies[32] {
    target: opt<@Vec2>;
    hp: i32;
  }`,
  { kind: "clean" },
  "region field typed opt<@R> (nullable embedded region handle)",
);

// ── Positive: opt<ptr<T>> — nested nullability on a raw pointer ──────

run(
  `region FreeSlot {
    next: opt<ptr<FreeSlot>>;
  }`,
  { kind: "clean" },
  "opt<ptr<T>> — nested nullable pointer field",
);

// ── Positive: non-null handle parameter — &region<X> shape ───────────

run(
  `region Players[8] {
    hp: i32;
  }
  fn read_hp(players: &region<Players>, idx: i32) -> i32
    effects { ReadRegion(Players) }
  {
    region.get $players[idx] .hp -> hp;
    return hp;
  }`,
  { kind: "clean" },
  "&region<X> parameter (non-null shared handle)",
);

// ── Positive: mutable non-null handle — &mut region<X> ───────────────

run(
  `region Players[8] {
    hp: i32;
  }
  fn set_hp(players: &mut region<Players>, idx: i32, new_hp: i32)
    effects { ReadRegion(Players), WriteRegion(Players) }
  {
    region.set $players[idx] .hp, new_hp;
  }`,
  { kind: "clean" },
  "&mut region<X> parameter (non-null exclusive handle)",
);

// ── Positive: is_null predicate on opt-typed field threads clean ─────

run(
  `region Vec2 { x: f32; y: f32; }
  region Enemies[16] {
    target: opt<@Vec2>;
  }
  fn check_target(enemies: &region<Enemies>, i: i32) -> i32
    effects { ReadRegion(Enemies) }
  {
    region.get $enemies[i] .target -> maybe_target;
    if is_null(maybe_target) {
      return -1;
    }
    return 0;
  }`,
  { kind: "clean" },
  "is_null() guard on opt<@R> field",
);

// ── Positive: opt<primitive> — nullable primitive (u32 example) ──────

run(
  `region Slot[4] {
    value: opt<u32>;
  }`,
  { kind: "clean" },
  "opt<u32> — nullable primitive field",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L4: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
