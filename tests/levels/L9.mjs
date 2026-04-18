// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 9 — Lifetime safety (use-after-free, QTT-erased)
//
// L9 attests that no reference is used after its owning allocation has
// been freed. The Idris2 proof layer
// (`src/abi/TypedWasm/ABI/Lifetime.idr`) carries the full soundness
// story with a `Lifetime.Outlives` preorder (`outlivesRefl`,
// `outlivesTrans`, the 7-constructor case analysis), the `loadSafe`
// proof term, and the behavioural lemmas `loadSafeOffset` +
// `loadSafeIrrelevant` — all added A4 (2026-04-18). L9 attestations
// live at type-checking time and are erased by QTT before code
// generation, so the emitted Wasm is identical to code written without
// lifetime tracking.
//
// There is intentionally NO ReScript diagnostic for "use after free"
// today: the analysis requires flow-sensitive lifetime reasoning that
// the Idris2 proof layer owns. Asserting such a diagnostic in this
// file would give false confidence.
//
// What this file's role IS:
//   - Certify that the canonical L9 surface shapes — allocate-then-
//     consume patterns using `own region<X>`, `region.alloc`,
//     `region.free` — parse + check clean in the ReScript pipeline.
//     The QTT-erased proof layer requires this carrier.
//   - Exercise the `own region<X>` handle-mode through parameters and
//     return types so regressions in handle-kind wiring surface here.
//
// Run: node tests/levels/L9.mjs

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

console.log("=== Level 9: Lifetime safety (use-after-free, QTT-erased) ===\n");

// ── Positive: `own region<X>` as a function return type ──────────────
// Allocating function returns an owning handle — the surface carrier
// for the Lifetime.Outlives reasoning on the Idris2 side.

run(
  `region Particle {
    hp: i32;
  }
  fn spawn() -> own region<Particle>
    effects { Alloc }
  {
    region.alloc Particle { hp = 100 } -> p;
    return p;
  }`,
  { kind: "clean" },
  "fn returning own region<Particle>",
);

// ── Positive: `own region<X>` as a function parameter (consumed) ─────

run(
  `region Particle {
    hp: i32;
  }
  fn despawn(p: own region<Particle>)
    effects { Free }
  {
    region.free $p;
  }`,
  { kind: "clean" },
  "fn consuming own region<Particle>",
);

// ── Positive: alloc-then-borrow-then-free lifecycle ──────────────────
// The Idris2 proof layer checks that `&mut p` borrow lifetime is
// strictly inside the `own p` lifetime; surface must parse + check
// clean for that obligation to be discharged.

run(
  `region Particle {
    hp: i32;
    ttl: f32;
  }
  fn spawn() -> own region<Particle>
    effects { Alloc }
  {
    region.alloc Particle { hp = 100, ttl = 5.0 } -> p;
    return p;
  }
  fn update(p: &mut region<Particle>, dt: f32)
    effects { ReadRegion(Particle), WriteRegion(Particle) }
  {
    region.get $p .ttl -> t;
    region.set $p .ttl, t - dt;
  }
  fn despawn(p: own region<Particle>)
    effects { Free }
  {
    region.free $p;
  }`,
  { kind: "clean" },
  "alloc → borrow-for-update → consume pipeline across three fns",
);

// ── Positive: lifetime-typed ptr field (opt<ptr<FreeSlot>>) ──────────
// Linked-list of free slots is the classic lifetime-carrying
// self-referential region shape. The parser admits it; the Idris2
// proof layer reasons about each next-pointer's outlives relationship.

run(
  `region FreeSlot {
    next: opt<ptr<FreeSlot>>;
  }
  region Arena[1024] {
    head: opt<ptr<FreeSlot>>;
    total: i32;
  }`,
  { kind: "clean" },
  "self-referential region with opt<ptr<...>> next field",
);

// ── Positive: shared read-only borrow of a long-lived region ─────────
// `&region<X>` is the short-lived borrow; the Idris2 proof layer
// ensures the borrow lifetime is shorter than the allocation.

run(
  `region Particle {
    hp: i32;
  }
  fn read_hp(p: &region<Particle>) -> i32
    effects { ReadRegion(Particle) }
  {
    region.get $p .hp -> hp;
    return hp;
  }`,
  { kind: "clean" },
  "&region<Particle> short-lived read borrow",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L9: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
