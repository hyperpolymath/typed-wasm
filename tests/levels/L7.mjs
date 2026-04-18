// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 7 — Aliasing safety (QTT-erased)
//
// L7 attests that a `&mut region<X>` (exclusive mutable borrow) and
// `unique<T>` (exclusive owning reference) genuinely alias nothing
// else in the program's static slice. This is the first of the
// research-tier levels that are PROVED in Idris2 and then erased by
// QTT (Quantitative Type Theory, quantity q=1) before code generation.
//
// There is intentionally no ReScript diagnostic for L7: the aliasing
// invariant is a global property of the program text that the ReScript
// parser + checker cannot decide on its own. The actual proof lives
// in:
//
//   src/abi/TypedWasm/ABI/Pointer.idr      (ExclusiveWitness, Unique)
//   src/abi/TypedWasm/ABI/Proofs.idr       (L7 attestation threading)
//
// What this file's role IS:
//   - Certify that the canonical L7 surface shapes — `&mut region<X>`,
//     `unique<T>`, coexistence of multiple `&region<X>` shared borrows —
//     parse + check clean in the ReScript pipeline. The proof layer
//     requires this carrier to reach it unmolested.
//   - Refuse to fabricate a "diagnostic" that does not actually fire
//     today. An absent diagnostic is the correct behaviour; writing a
//     test that expected one would give false confidence.
//
// Run: node tests/levels/L7.mjs

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

console.log("=== Level 7: Aliasing safety (QTT-erased) ===\n");

// ── Positive: &mut region<X> — exclusive mutable borrow ──────────────

run(
  `region Particle {
    pos_x: f32;
    pos_y: f32;
  }
  fn update(p: &mut region<Particle>, dt: f32)
    effects { ReadRegion(Particle), WriteRegion(Particle) }
  {
    region.get $p .pos_x -> px;
    region.set $p .pos_x, px;
  }`,
  { kind: "clean" },
  "&mut region<Particle> — exclusive mutable borrow parameter",
);

// ── Positive: unique<T> field — exclusive owning reference ───────────

run(
  `region Inner {
    value: i32;
  }
  region Holder {
    owned: unique<ptr<Inner>>;
  }`,
  { kind: "clean" },
  "unique<ptr<Inner>> field — exclusive owning pointer",
);

// ── Positive: two distinct &region<X> shared borrows coexist ─────────
// Two shared borrows of the same region are allowed by L7 — the
// exclusivity obligation only binds &mut and unique.

run(
  `region Particle {
    pos_x: f32;
    pos_y: f32;
  }
  fn read_twice(
    a: &region<Particle>,
    b: &region<Particle>
  ) -> f32
    effects { ReadRegion(Particle) }
  {
    region.get $a .pos_x -> x1;
    region.get $b .pos_x -> x2;
    return x1;
  }`,
  { kind: "clean" },
  "two &region<Particle> shared borrows as parameters",
);

// ── Positive: &region<X> and &mut region<Y> on different regions ─────
// Aliasing reasoning is per-region; two handles to DIFFERENT regions
// cannot alias and therefore both shapes coexist freely.

run(
  `region Players[32] { hp: i32; }
  region Enemies[32] { damage: i32; }
  fn fight(
    players: &mut region<Players>,
    enemies: &region<Enemies>,
    i: i32
  )
    effects { ReadRegion(Players), WriteRegion(Players), ReadRegion(Enemies) }
  {
    region.get $enemies[i] .damage -> dmg;
    region.get $players[i] .hp -> hp;
    region.set $players[i] .hp, hp - dmg;
  }`,
  { kind: "clean" },
  "&mut region<Players> + &region<Enemies> on distinct regions",
);

// ── Positive: ref<T> field — explicit borrowing pointer ──────────────

run(
  `region Target {
    value: i32;
  }
  region Holder {
    borrowed: ref<ptr<Target>>;
  }`,
  { kind: "clean" },
  "ref<ptr<Target>> field — explicit borrow pointer kind",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L7: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
