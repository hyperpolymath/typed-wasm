// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 10 — Linearity (exactly-once resource usage, QTT-erased)
//
// L10 attests that every linearly-typed resource — an `own region<X>`
// handle, a `unique<T>` owning pointer — is consumed EXACTLY ONCE
// along every execution path. Dropping it is forbidden (would leak),
// and consuming it twice is forbidden (double-free). The Idris2 proof
// layer (`src/abi/TypedWasm/ABI/Linear.idr`) carries the QTT-native
// q=1 quantity reasoning plus the propositional state-machine layer
// added A3 (2026-04-18): `LinHandleU Fresh/Consumed tok`, the
// `consume` state transition, and the theorems `distinctUsage`,
// `consumePreservesData`, `noReuse`, `noReuseEcho`.
//
// L10 is the third of the three QTT-erased levels (L7 + L9 + L10).
// As with those, the ReScript checker has NO diagnostic that fires
// on a "handle consumed twice" or "handle dropped without free"
// program text today: the analysis is Idris2-side, lifted by QTT,
// and entirely erased before code generation. Asserting such a
// diagnostic here would give false confidence.
//
// What this file's role IS:
//   - Certify that the canonical L10 surface shapes — `own region<X>`
//     round-trip through a function pair (spawn → despawn), with the
//     handle exactly-once-threaded — parse + check clean.
//   - Exercise the `region.alloc` / `region.free` statement pair, the
//     two sides of the linearity contract.
//
// Run: node tests/levels/L10.mjs

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

console.log("=== Level 10: Linearity (exactly-once, QTT-erased) ===\n");

// ── Positive: region.alloc → owning handle → region.free sequence ────
// Classic L10 shape: the handle is created, threaded, consumed.
// At proof-time, QTT q=1 discharges the exactly-once obligation.

run(
  `region Particle {
    hp: i32;
  }
  fn spawn() -> own region<Particle>
    effects { Alloc }
  {
    region.alloc Particle { hp = 100 } -> p;
    return p;
  }
  fn despawn(p: own region<Particle>)
    effects { Free }
  {
    region.free $p;
  }`,
  { kind: "clean" },
  "spawn/despawn pair — canonical linear handle thread",
);

// ── Positive: unique<T> field — owning-once pointer inside a region ──
// `unique<ptr<Inner>>` carries the same q=1 discipline for non-region
// owning pointers.

run(
  `region Inner {
    v: i32;
  }
  region Outer {
    owned: unique<ptr<Inner>>;
  }`,
  { kind: "clean" },
  "unique<ptr<Inner>> field — owning-once pointer",
);

// ── Positive: own handle passed to a function (consumed) ─────────────
// A function can take an owning handle as a parameter — the callee
// is obliged to consume it (free, forward, or store). Surface carrier.

run(
  `region Resource {
    id: i32;
  }
  fn make() -> own region<Resource>
    effects { Alloc }
  {
    region.alloc Resource { id = 1 } -> r;
    return r;
  }
  fn release(r: own region<Resource>)
    effects { Free }
  {
    region.free $r;
  }
  fn pipeline()
    effects { Alloc, Free }
  {
    let r : own region<Resource> = make();
    release(r);
  }`,
  { kind: "clean" },
  "pipeline: alloc-in-callee, consume-in-callee",
);

// ── Positive: alloc with field init block + multiple typed fields ────
// Exercises the `region.alloc T { f = v, g = w } -> handle;` shape.

run(
  `region Bundle {
    a: i32;
    b: f32;
    c: bool;
  }
  fn mint() -> own region<Bundle>
    effects { Alloc }
  {
    region.alloc Bundle { a = 1, b = 2.0, c = true } -> b;
    return b;
  }`,
  { kind: "clean" },
  "region.alloc with multi-field init block",
);

// ── Positive: linearly-typed free-list self-reference ────────────────
// A linked free list: each slot's `next` is a linearly owned pointer
// to the next free slot. Classic linear-types arena shape.

run(
  `region FreeSlot {
    next: opt<ptr<FreeSlot>>;
  }
  region Arena[256] {
    free_head: opt<ptr<FreeSlot>>;
  }`,
  { kind: "clean" },
  "linear free-list arena (linearly-typed self-reference)",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L10: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
