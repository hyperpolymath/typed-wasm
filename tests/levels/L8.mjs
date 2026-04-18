// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Level 8 — Effect-tracking (Read / Write / Alloc / Free / Region-*)
//
// L8 attests that every function declares — and composition-respects —
// the memory effects it performs. The Idris2 proof layer
// (`src/abi/TypedWasm/ABI/Effects.idr`) carries the full lattice with
// `EffectSubsumes` preorder, `effectSubsumesRefl`, `hasEffectTrans`,
// `subsumeTrans`, `hasEffectCombineL/R`, `subsumePrepend/Append`, and
// the flagship `subsumeCompose` (A5, 2026-04-18) — so L8 attestations
// compose structurally.
//
// Surface exposure in the ReScript checker:
//   - An `effects { ... }` clause is OPTIONAL in the grammar: a
//     function without one parses, and `effects`/`caps` are both
//     `None` in the AST. This matches the examples/ fixtures, which
//     include functions with and without explicit clauses.
//   - The v1.1 split-effects form (`effects { memory: { Read, Write },
//     caps: { read_file, web_fetch } }`) populates both `effects` and
//     `caps`; the checker accepts this without L8-specific diagnostics
//     (the `caps` sub-list is the L15 carrier, see L15 in the spec).
//   - There is NO "function performs undeclared effect" diagnostic in
//     the ReScript checker today. That analysis is Idris2-side — the
//     `effectSubsumes` witness is built at proof-time from the
//     declared effect set against the body's actually-performed set.
//     Asserting a diagnostic that does not fire would give false
//     confidence.
//
// What this file's role IS:
//   - Certify that effect-clause shapes (missing, flat, split,
//     region-qualified) parse + check clean.
//   - Exercise every effect keyword the grammar admits so regressions
//     in parser → AST → checker wiring surface here.
//
// Run: node tests/levels/L8.mjs

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

console.log("=== Level 8: Effect-tracking (Read/Write/Alloc/Free) ===\n");

// ── Positive: flat effects clause with region-qualified effects ──────

run(
  `region Players[16] { hp: i32; }
  fn read_hp(players: &region<Players>, idx: i32) -> i32
    effects { ReadRegion(Players) }
  {
    region.get $players[idx] .hp -> hp;
    return hp;
  }`,
  { kind: "clean" },
  "flat effects { ReadRegion(Players) }",
);

// ── Positive: multi-effect flat clause — read + write ───────────────

run(
  `region Players[16] { hp: i32; }
  fn damage(players: &mut region<Players>, idx: i32, amount: i32)
    effects { ReadRegion(Players), WriteRegion(Players) }
  {
    region.get $players[idx] .hp -> hp;
    region.set $players[idx] .hp, hp - amount;
  }`,
  { kind: "clean" },
  "flat effects { ReadRegion, WriteRegion } pair",
);

// ── Positive: Alloc / Free memory effects ────────────────────────────

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
  "Alloc / Free memory-lifecycle effect pair",
);

// ── Positive: v1.1 split-effects form — memory + caps sub-clauses ────
// Capabilities named in a `caps: {...}` sub-clause must be declared
// at the enclosing module scope (L15-B — this fires at v1.4, the
// current checker version; see L15 for the direct L15 surface). L8
// tests declare the caps up front so the split-effects carrier can be
// exercised without tripping the L15 scoping check.

run(
  `capability read_file;
  capability web_fetch;
  fn action() effects { memory: { Read, Write }, caps: { read_file, web_fetch } } {
    return;
  }`,
  { kind: "clean" },
  "v1.1 split `effects { memory: {...}, caps: {...} }` (with L15 decls)",
);

// ── Positive: missing effects clause — grammar accepts it ────────────
// The parser treats the effects clause as optional; the Idris2 proof
// layer fills in the empty effect set on behalf of such a function.

run(
  `fn noop() {
    return;
  }`,
  { kind: "clean" },
  "function with no effects clause (empty effect set)",
);

// ── Positive: flat bare effects (no region qualification) ────────────
// `Read` / `Write` without a region name is the v1.0 flat effect.

run(
  `fn touch() effects { Read, Write } {
    return;
  }`,
  { kind: "clean" },
  "flat effects { Read, Write } (no region qualification)",
);

// ── Positive: v1.1 split with ONLY caps sub-clause ────────────────────
// `caps: {...}` is the load-bearing L15 carrier but parses + checks
// clean at v1.1 where it is opaque.

run(
  `capability web_fetch;
  fn fetch_only() effects { memory: { Read }, caps: { web_fetch } } {
    return;
  }`,
  { kind: "clean" },
  "split effects with single memory + single cap (with L15 decl)",
);

// ── Summary ──────────────────────────────────────────────────────────

console.log(`\n--- L8: ${passed} passed, ${failed} failed ---`);
process.exit(failed > 0 ? 1 : 0);
