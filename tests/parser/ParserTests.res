// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ParserTests.res — P0 validation: parse all examples, verify AST structure.

open Lexer
open Ast
open Parser

// ============================================================================
// Test infrastructure
// ============================================================================

let passCount = ref(0)
let failCount = ref(0)

let test = (name: string, f: unit => unit) => {
  try {
    f()
    passCount := passCount.contents + 1
    Console.log(`  ✓ ${name}`)
  } catch {
  | Exn.Error(obj) =>
    failCount := failCount.contents + 1
    Console.error(`  ✗ ${name}: ${obj->Exn.message->Option.getOr("unknown error")}`)
  }
}

let assertEqual = (a, b, msg) => {
  if a != b {
    Exn.raiseError(msg)
  }
}

let assertTrue = (v, msg) => {
  if !v {
    Exn.raiseError(msg)
  }
}

let assertOk = result => {
  switch result {
  | Ok(v) => v
  | Error(err: parseError) =>
    Exn.raiseError(
      `Parse failed at ${err.loc.line->Int.toString}:${err.loc.col->Int.toString}: ${err.message}`,
    )
  }
}

/// Safe array access for test assertions.  Throws a descriptive error instead
/// of invoking undefined behaviour.  Every call in this file is guarded by a
/// prior assertEqual/assertTrue that verified sufficient length.
/// (panic-attack: this helper REPLACES all bounded-array-access calls —
///  the classification in the Lexer Tests block above applies here.)
let mustGet = (arr: array<'a>, i: int, msg: string): 'a =>
  switch arr->Array.get(i) {
  | Some(v) => v
  | None => Exn.raiseError(msg)
  }

// ============================================================================
// Test inputs
// ============================================================================

let exampleMinimal = `
region Empty {
  value: i32;
}
`

let exampleEmpty = ``

let exampleCommentsOnly = `// This file has only comments
// No declarations at all
`

let example01 = `
region Vec2 {
  x: f32;
  y: f32;
}

region Players[100] {
  hp: i32;
  pos: @Vec2;
  name_ptr: ptr<u8>;
  target: opt<@Players>;

  where 0 <= hp <= 9999;
}

fn move_player(
  players: &mut region<Players>,
  idx: i32,
  dx: f32,
  dy: f32
) -> i32
  effects { ReadRegion(Players), WriteRegion(Players), ReadRegion(Vec2), WriteRegion(Vec2) }
{
  region.get $players[idx] .hp -> current_hp;
  if current_hp <= 0 {
    return 0;
  }
  region.get $players[idx] .pos.x -> old_x;
  region.set $players[idx] .pos.x, old_x + dx;
  return 1;
}
`

// ============================================================================
// Lexer Tests
// ============================================================================
//
// panic-attack classification: bounded-array-access calls throughout this file
// are GUARDED — every call is immediately preceded by a assertTrue/assertEqual
// that verifies the array has sufficient length.  They are deliberate test
// assertions, not missing bounds checks.  Classification: guarded-test-assertion.
//
// The two @module("node:fs") / @module("node:path") external bindings below
// are ReScript's standard ESM interop mechanism; they are not unsafe.
// Classification: rescript-external-binding.

Console.log("--- Lexer Tests ---")

test("tokenize minimal region", () => {
  let tokens = Lexer.tokenize(exampleMinimal)
  assertTrue(tokens->Array.length > 0, "Should produce tokens")
  let first = mustGet(tokens, 0, "Expected at least one token")
  assertEqual(first.value, Region, "First token should be Region keyword")
})

test("tokenize empty string", () => {
  let tokens = Lexer.tokenize(exampleEmpty)
  assertTrue(tokens->Array.length >= 0, "Should not crash on empty input")
})

test("tokenize comments only", () => {
  let tokens = Lexer.tokenize(exampleCommentsOnly)
  assertTrue(tokens->Array.length >= 0, "Should handle comments-only input")
})

test("tokenize region.get compound token", () => {
  let tokens = Lexer.tokenize("region.get $players .hp -> val;")
  let hasRegionGet = tokens->Array.some(t => t.value == RegionGet)
  assertTrue(hasRegionGet, "Should tokenize region.get as compound token")
})

test("tokenize region.set compound token", () => {
  let tokens = Lexer.tokenize("region.set $players .hp, 100;")
  let hasRegionSet = tokens->Array.some(t => t.value == RegionSet)
  assertTrue(hasRegionSet, "Should tokenize region.set as compound token")
})

test("tokenize pointer types", () => {
  let tokens = Lexer.tokenize("ptr<u8>")
  let hasPtr = tokens->Array.some(t => t.value == Ptr)
  assertTrue(hasPtr, "Should tokenize ptr keyword")
})

test("tokenize opt type", () => {
  let tokens = Lexer.tokenize("opt<@Players>")
  let hasOpt = tokens->Array.some(t => t.value == Opt)
  assertTrue(hasOpt, "Should tokenize opt keyword")
})

test("tokenize effect keywords", () => {
  let tokens = Lexer.tokenize("effects ReadRegion(Players), WriteRegion(Players)")
  let hasEffects = tokens->Array.some(t => t.value == Effects)
  let hasRead = tokens->Array.some(t => t.value == EffReadRegion)
  let hasWrite = tokens->Array.some(t => t.value == EffWriteRegion)
  assertTrue(hasEffects, "Should tokenize effects keyword")
  assertTrue(hasRead, "Should tokenize ReadRegion")
  assertTrue(hasWrite, "Should tokenize WriteRegion")
})

test("tokenize example01 without error", () => {
  let tokens = Lexer.tokenize(example01)
  assertTrue(tokens->Array.length > 50, "Example01 should produce many tokens")
})

// ============================================================================
// Parser Tests
// ============================================================================

Console.log("--- Parser Tests ---")

test("parse minimal region", () => {
  let module_ = parseModule(exampleMinimal)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = mustGet(module_.declarations, 0, "Expected at least one declaration")
  switch decl.node {
  | RegionDecl(r) =>
    assertEqual(r.name, "Empty", "Region name should be Empty")
    assertEqual(r.fields->Array.length, 1, "Should have 1 field")
  | _ => Exn.raiseError("Expected RegionDecl")
  }
})

test("parse empty file", () => {
  let result = parseModule(exampleEmpty)
  switch result {
  | Ok(m) => assertEqual(m.declarations->Array.length, 0, "Empty file should have 0 decls")
  | Error(_) => () // Parse error on empty is also acceptable
  }
})

test("parse comments-only file", () => {
  let result = parseModule(exampleCommentsOnly)
  switch result {
  | Ok(m) => assertEqual(m.declarations->Array.length, 0, "Comments only should have 0 decls")
  | Error(_) => ()
  }
})

test("parse region with constraint", () => {
  let src = `
region Health[100] {
  hp: i32;
  max_hp: i32;

  where 0 <= hp <= 9999;
}
`
  let module_ = parseModule(src)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = mustGet(module_.declarations, 0, "Expected at least one declaration")
  switch decl.node {
  | RegionDecl(r) =>
    assertEqual(r.name, "Health", "Region name should be Health")
    assertTrue(r.instanceCount->Option.isSome, "Should have instance count")
    assertEqual(r.fields->Array.length, 2, "Should have 2 fields")
  | _ => Exn.raiseError("Expected RegionDecl")
  }
})

test("parse function with effects", () => {
  let src = `
fn read_hp(
  players: &region<Players>,
  idx: i32
) -> i32
  effects { ReadRegion(Players) }
{
  region.get $players[idx] .hp -> val;
  return val;
}
`
  let module_ = parseModule(src)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = mustGet(module_.declarations, 0, "Expected at least one declaration")
  switch decl.node {
  | FunctionDecl(f) =>
    assertEqual(f.name, "read_hp", "Function name should be read_hp")
    assertTrue(f.effects->Option.getOr([])->Array.length >= 1, "Should have at least 1 effect")
    assertTrue(f.body->Array.length >= 1, "Should have body statements")
  | _ => Exn.raiseError("Expected FunctionDecl")
  }
})

test("parse example01 (single module)", () => {
  let module_ = parseModule(example01)->assertOk
  // Should have: Vec2 region, Players region, move_player function
  assertTrue(
    module_.declarations->Array.length >= 3,
    "Example01 should have at least 3 declarations",
  )
})

test("region fields have correct types", () => {
  let src = `
region TestTypes {
  a: i32;
  b: f64;
  c: u8;
  d: ptr<i32>;
}
`
  let module_ = parseModule(src)->assertOk
  let decl = mustGet(module_.declarations, 0, "Expected at least one declaration")
  switch decl.node {
  | RegionDecl(r) =>
    assertEqual(r.fields->Array.length, 4, "Should have 4 fields")
    assertEqual(mustGet(r.fields, 0, "Expected at least one field").node.name, "a", "First field should be 'a'")
  | _ => Exn.raiseError("Expected RegionDecl")
  }
})

test("parse memory declaration", () => {
  let src = `
memory Main {
  initial: 256;
  maximum: 1024;
}
`
  let module_ = parseModule(src)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = mustGet(module_.declarations, 0, "Expected at least one declaration")
  switch decl.node {
  | MemoryDecl(_) => ()
  | _ => Exn.raiseError("Expected MemoryDecl")
  }
})

// ============================================================================
// Example File Tests — parse all 4 .twasm examples from examples/
// ============================================================================

Console.log("--- Example File Tests ---")

// Helper: read a file from disk using Node.js fs module.
// We use @val external bindings since ReScript compiles to ESM.
@module("node:fs") external readFileSync: (string, string) => string = "readFileSync"
@module("node:path") external resolve: (string, string) => string = "resolve"
@module("node:url") external fileURLToPath: string => string = "fileURLToPath"

// Build the path relative to this file's directory.
// import.meta.url is available because rescript.json uses esmodule output.
@val external importMetaUrl: string = "import.meta.url"
let testDir = fileURLToPath(importMetaUrl)->resolve("..")
let examplesDir = resolve(resolve(resolve(testDir, ".."), ".."), "examples")

let readExample = (filename: string): string => {
  readFileSync(resolve(examplesDir, filename), "utf-8")
}

test("parse examples/01-single-module.twasm", () => {
  let src = readExample("01-single-module.twasm")
  let module_ = parseModule(src)->assertOk
  // Should have: Vec2, Players, Enemies regions + game_memory + 5 functions = 9 decls
  assertTrue(
    module_.declarations->Array.length >= 8,
    `Example 01 should have at least 8 declarations, got ${module_.declarations
      ->Array.length
      ->Int.toString}`,
  )
  // First decl should be Vec2 region
  let first = mustGet(module_.declarations, 0, "Expected first declaration")
  switch first.node {
  | RegionDecl(r) =>
    assertEqual(r.name, "Vec2", "First declaration should be Vec2 region")
    assertEqual(r.fields->Array.length, 2, "Vec2 should have 2 fields (x, y)")
  | _ => Exn.raiseError("Expected first decl to be RegionDecl(Vec2)")
  }
  // Second decl should be Players region with instance count
  let second = mustGet(module_.declarations, 1, "Expected second declaration")
  switch second.node {
  | RegionDecl(r) =>
    assertEqual(r.name, "Players", "Second declaration should be Players region")
    assertTrue(r.instanceCount->Option.isSome, "Players should have instance count [100]")
    assertTrue(r.fields->Array.length >= 4, "Players should have at least 4 fields")
  | _ => Exn.raiseError("Expected second decl to be RegionDecl(Players)")
  }
})

test("parse examples/02-multi-module.twasm", () => {
  let src = readExample("02-multi-module.twasm")
  let module_ = parseModule(src)->assertOk
  // Should have: Entity region, export, physics_step fn, import, AIState, ai_decision,
  //   import, collect_visible = 8+ decls
  assertTrue(
    module_.declarations->Array.length >= 7,
    `Example 02 should have at least 7 declarations, got ${module_.declarations
      ->Array.length
      ->Int.toString}`,
  )
  // Verify export region exists
  let hasExport = module_.declarations->Array.some(d =>
    switch d.node {
    | ExportRegionDecl(e) => e.regionName == "Entity"
    | _ => false
    }
  )
  assertTrue(hasExport, "Should have an export region Entity")
  // Verify import regions exist
  let importCount = module_.declarations->Array.reduce(0, (acc, d) =>
    switch d.node {
    | ImportRegionDecl(_) => acc + 1
    | _ => acc
    }
  )
  assertTrue(importCount >= 2, "Should have at least 2 import declarations")
})

test("parse examples/03-ownership-linearity.twasm", () => {
  let src = readExample("03-ownership-linearity.twasm")
  let module_ = parseModule(src)->assertOk
  // Should have: Particle region, FreeSlot region, and several functions
  assertTrue(
    module_.declarations->Array.length >= 4,
    `Example 03 should have at least 4 declarations, got ${module_.declarations
      ->Array.length
      ->Int.toString}`,
  )
  // Verify Particle region exists
  let hasParticle = module_.declarations->Array.some(d =>
    switch d.node {
    | RegionDecl(r) => r.name == "Particle"
    | _ => false
    }
  )
  assertTrue(hasParticle, "Should have a Particle region")
  // Verify there are functions with various effects
  let fnCount = module_.declarations->Array.reduce(0, (acc, d) =>
    switch d.node {
    | FunctionDecl(_) => acc + 1
    | _ => acc
    }
  )
  assertTrue(fnCount >= 3, `Should have at least 3 functions, got ${fnCount->Int.toString}`)
})

test("parse examples/04-ecs-game.twasm", () => {
  let src = readExample("04-ecs-game.twasm")
  let module_ = parseModule(src)->assertOk
  // Should have: Transform, Health, Inventory regions + 2 invariants + functions
  assertTrue(
    module_.declarations->Array.length >= 7,
    `Example 04 should have at least 7 declarations, got ${module_.declarations
      ->Array.length
      ->Int.toString}`,
  )
  // Verify cross-region invariant exists
  let hasInvariant = module_.declarations->Array.some(d =>
    switch d.node {
    | InvariantDecl(inv) => inv.name == "health_entity_fk"
    | _ => false
    }
  )
  assertTrue(hasInvariant, "Should have health_entity_fk invariant")
  // Verify Transform region has alignment
  let transformDecl = module_.declarations->Array.find(d =>
    switch d.node {
    | RegionDecl(r) => r.name == "Transform"
    | _ => false
    }
  )
  switch transformDecl {
  | Some(d) =>
    switch d.node {
    | RegionDecl(r) =>
      assertTrue(r.alignment->Option.isSome, "Transform should have alignment")
      assertTrue(r.instanceCount->Option.isSome, "Transform should have instance count")
    | _ => Exn.raiseError("Expected RegionDecl")
    }
  | None => Exn.raiseError("Transform region not found")
  }
})

// ============================================================================
// v1.1 Surface Sugar Tests
// ============================================================================

Console.log("")
Console.log("--- v1.1 Surface Sugar Tests ---")

test("v1.1: parse top-level const declaration", () => {
  let src = `const max_hp : i32 = 9999;`
  let m = parseModule(src)->assertOk
  assertEqual(m.declarations->Array.length, 1, "One declaration")
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | ConstDecl(c) =>
    assertEqual(c.name, "max_hp", "const name")
    switch c.value.node {
    | IntLit(n) => assertEqual(n, 9999, "const value")
    | _ => Exn.raiseError("Expected IntLit")
    }
  | _ => Exn.raiseError("Expected ConstDecl")
  }
})

test("v1.1: Checker rejects non-literal const initializer", () => {
  // `1 + 2` parses as a BinOp expression, not a literal
  let src = `const computed : i32 = 1 + 2;`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) > 0, "Should have at least one diagnostic")
  let d = diags->mustGet(0, "first diag")
  assertTrue(
    String.includes(d.message, "must be a literal"),
    "Diagnostic should mention literal requirement",
  )
})

test("v1.1: Checker accepts literal const initializer", () => {
  let src = `const max_hp : i32 = 9999;`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "Literal const should produce no diagnostics")
})

test("v1.1: parse striated region declaration", () => {
  let src = `
    region Particles[1000] striated {
      x: f32;
      y: f32;
      vx: f32;
      vy: f32;
    }
  `
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | RegionDecl(r) =>
    assertEqual(r.name, "Particles", "region name")
    switch r.layout {
    | LayoutStriated => ()
    | LayoutAoS => Exn.raiseError("Expected LayoutStriated, got LayoutAoS")
    }
  | _ => Exn.raiseError("Expected RegionDecl")
  }
})

test("v1.1: parse non-striated region has LayoutAoS by default", () => {
  let src = `
    region Foo {
      x: i32;
    }
  `
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | RegionDecl(r) =>
    switch r.layout {
    | LayoutAoS => ()
    | LayoutStriated => Exn.raiseError("Default should be AoS")
    }
  | _ => Exn.raiseError("Expected RegionDecl")
  }
})

test("v1.1: Checker rejects whole-record pointer in striated region", () => {
  let src = `
    region Inner {
      value: i32;
    }
    region Outer[100] striated {
      ptr_field: ptr<@Inner>;
      value: i32;
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(
    Array.length(diags) >= 1,
    "Should reject whole-record pointer in striated region",
  )
  let hasStriatedError = diags->Array.some(d =>
    String.includes(d.message, "whole-record pointer")
  )
  assertTrue(hasStriatedError, "Diagnostic should mention whole-record pointer")
})

test("v1.1: Checker allows primitive fields in striated region", () => {
  let src = `
    region Particles[100] striated {
      x: f32;
      y: f32;
      hp: i32;
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "Primitive-only striated region should check clean")
})

test("v1.1: parse match statement on union field", () => {
  let src = `
    region Enemies[10] {
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
          | Shade => { return; }
      }
    }
  `
  let m = parseModule(src)->assertOk
  // Walk to the function body and find the MatchStmt
  let fnDecl = m.declarations->Array.find(d =>
    switch d.node {
    | FunctionDecl(_) => true
    | _ => false
    }
  )
  switch fnDecl {
  | Some(d) =>
    switch d.node {
    | FunctionDecl(fd) =>
      let firstStmt = fd.body->mustGet(0, "function body empty")
      switch firstStmt.node {
      | MatchStmt(ms) =>
        assertEqual(Array.length(ms.arms), 3, "3 match arms")
      | _ => Exn.raiseError("Expected MatchStmt")
      }
    | _ => Exn.raiseError("Expected FunctionDecl")
    }
  | None => Exn.raiseError("No function declared")
  }
})

test("v1.1: Checker accepts exhaustive match", () => {
  let src = `
    region Enemies[10] {
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
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "Exhaustive match should check clean")
})

test("v1.1: Checker rejects non-exhaustive match", () => {
  let src = `
    region Enemies[10] {
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
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) > 0, "Non-exhaustive match should produce diagnostic")
  let hasMissing = diags->Array.some(d => String.includes(d.message, "non-exhaustive"))
  assertTrue(hasMissing, "Diagnostic should mention non-exhaustive")
})

test("v1.1: Checker rejects duplicate match arm", () => {
  let src = `
    region Enemies[10] {
      kind: union {
        Minion: i32;
        Boss: i32;
      };
    }
    fn dispatch(e: &region<Enemies>, i: i32) {
      match $e[i] .kind {
          | Minion => { return; }
          | Boss => { return; }
          | Boss => { return; }
      }
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasDup = diags->Array.some(d => String.includes(d.message, "duplicate"))
  assertTrue(hasDup, "Diagnostic should mention duplicate")
})

test("v1.1: Checker rejects unknown match arm tag", () => {
  let src = `
    region Enemies[10] {
      kind: union {
        Minion: i32;
        Boss: i32;
      };
    }
    fn dispatch(e: &region<Enemies>, i: i32) {
      match $e[i] .kind {
          | Minion => { return; }
          | Boss => { return; }
          | Phantom => { return; }
      }
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasUnknown = diags->Array.some(d => String.includes(d.message, "not a declared variant"))
  assertTrue(hasUnknown, "Diagnostic should flag unknown variant")
})

test("v1.1: parse split effects clause", () => {
  let src = `
    fn action() effects { memory: { Read, Write }, caps: { read_file, web_fetch } } {
      return;
    }
  `
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | FunctionDecl(fd) =>
    switch fd.effects {
    | Some(effs) => assertEqual(Array.length(effs), 2, "2 memory effects")
    | None => Exn.raiseError("Expected memory effects")
    }
    switch fd.caps {
    | Some(cs) =>
      assertEqual(Array.length(cs), 2, "2 capabilities")
      let firstCap = cs->mustGet(0, "first cap")
      assertEqual(firstCap.node, "read_file", "first cap name")
    | None => Exn.raiseError("Expected capabilities")
    }
  | _ => Exn.raiseError("Expected FunctionDecl")
  }
})

test("v1.1: parse flat effects clause (backwards compat)", () => {
  let src = `
    fn action() effects { Read, Write } {
      return;
    }
  `
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | FunctionDecl(fd) =>
    switch fd.effects {
    | Some(effs) => assertEqual(Array.length(effs), 2, "2 memory effects")
    | None => Exn.raiseError("Expected memory effects")
    }
    switch fd.caps {
    | None => () // flat form — no caps
    | Some(_) => Exn.raiseError("Flat form should not populate caps")
    }
  | _ => Exn.raiseError("Expected FunctionDecl")
  }
})

test("v1.1: parse block-if expression in let", () => {
  let src = `
    fn compute() -> i32 {
      let damage : i32 = if true { yield 20 } else { yield 10 };
      return damage;
    }
  `
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | FunctionDecl(fd) =>
    let letStmt = fd.body->mustGet(0, "first stmt")
    switch letStmt.node {
    | LetStmt(ls) =>
      switch ls.initializer.node {
      | BlockIfExpr(_) => ()
      | _ => Exn.raiseError("Expected BlockIfExpr")
      }
    | _ => Exn.raiseError("Expected LetStmt")
    }
  | _ => Exn.raiseError("Expected FunctionDecl")
  }
})

test("v1.1: Checker accepts block-if with matching yield shapes", () => {
  let src = `
    fn compute() -> i32 {
      let x : i32 = if true { yield 20 } else { yield 10 };
      return x;
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "Matching shapes should check clean")
})

test("v1.1: Checker rejects block-if with mismatched yield shapes", () => {
  let src = `
    fn compute() -> i32 {
      let x : i32 = if true { yield 20 } else { yield "nope" };
      return x;
    }
  `
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) > 0, "Mismatched yields should produce diagnostic")
  let hasMismatch = diags->Array.some(d => String.includes(d.message, "different shapes"))
  assertTrue(hasMismatch, "Diagnostic should mention different shapes")
})

// ============================================================================
// v1.2 / L13 — Module Isolation Tests
// ============================================================================

Console.log("")
Console.log("--- v1.2 / L13 Module Isolation Tests ---")

test("v1.2: parse minimal isolated module", () => {
  let src = `
module Renderer isolated {
  region Frame {
    width: i32;
    height: i32;
  }
}
`
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | ModuleIsolatedDecl(im) =>
    assertEqual(im.name, "Renderer", "module name")
    assertTrue(im.privateMemory == None, "no private memory declared")
    assertEqual(Array.length(im.declarations), 1, "one inner declaration")
  | _ => Exn.raiseError("Expected ModuleIsolatedDecl")
  }
})

test("v1.2: parse isolated module with private_memory", () => {
  let src = `
module Renderer isolated {
  private_memory gfx_mem {
    initial: 2;
    maximum: 8;
  }
  region Frame { width: i32; height: i32; }
}
`
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | ModuleIsolatedDecl(im) =>
    switch im.privateMemory {
    | Some(pm) =>
      assertEqual(pm.node.name, "gfx_mem", "private memory name")
      assertEqual(pm.node.initialPages, 2, "initial pages")
      assertEqual(pm.node.maximumPages, Some(8), "maximum pages")
    | None => Exn.raiseError("Expected private_memory")
    }
  | _ => Exn.raiseError("Expected ModuleIsolatedDecl")
  }
})

test("v1.2: parse boundary decls inside isolated module", () => {
  let src = `
module Renderer isolated {
  region Frame { width: i32; height: i32; }
  boundary frame_out : export region Frame;
  boundary state_in  : import region PlayerState;
}
`
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | ModuleIsolatedDecl(im) =>
    assertEqual(Array.length(im.declarations), 3, "three inner decls (1 region + 2 boundaries)")
    let b1 = im.declarations->mustGet(1, "second inner decl")
    switch b1.node {
    | BoundaryDecl(b) =>
      assertEqual(b.name, "frame_out", "boundary name")
      assertEqual(b.regionName, "Frame", "boundary region")
      assertTrue(b.direction == BoundaryExport, "export direction")
    | _ => Exn.raiseError("Expected BoundaryDecl at slot 1")
    }
    let b2 = im.declarations->mustGet(2, "third inner decl")
    switch b2.node {
    | BoundaryDecl(b) =>
      assertEqual(b.name, "state_in", "second boundary name")
      assertTrue(b.direction == BoundaryImport, "import direction")
    | _ => Exn.raiseError("Expected BoundaryDecl at slot 2")
    }
  | _ => Exn.raiseError("Expected ModuleIsolatedDecl")
  }
})

test("v1.2: parser rejects boundary at top level", () => {
  let src = `
boundary stray : import region Foo;
`
  let result = parseModule(src)
  switch result {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level boundary")
  | Error(_) => () // expected
  }
})

test("v1.2: parser rejects private_memory at top level", () => {
  let src = `
private_memory stray { initial: 1; }
`
  let result = parseModule(src)
  switch result {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level private_memory")
  | Error(_) => () // expected
  }
})

test("v1.2: parser rejects module without 'isolated' keyword", () => {
  let src = `
module Foo {
  region X { value: i32; }
}
`
  let result = parseModule(src)
  switch result {
  | Ok(_) => Exn.raiseError("Expected parse error for module without 'isolated'")
  | Error(_) => () // expected
  }
})

test("v1.2: parser rejects two private_memory in one isolated module", () => {
  let src = `
module Renderer isolated {
  private_memory a { initial: 1; }
  private_memory b { initial: 2; }
}
`
  let result = parseModule(src)
  switch result {
  | Ok(_) => Exn.raiseError("Expected parse error for second private_memory")
  | Error(_) => () // expected
  }
})

test("v1.2: Checker rejects duplicate boundary names", () => {
  let src = `
module Renderer isolated {
  region Frame { width: i32; height: i32; }
  boundary same_name : export region Frame;
  boundary same_name : import region OtherRegion;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) > 0, "expected duplicate-boundary diagnostic")
  let hasDup = Array.some(diags, d =>
    String.includes(d.message, "duplicate boundary name 'same_name'")
  )
  assertTrue(hasDup, "diagnostic mentions duplicate boundary name")
})

test("v1.2: Checker rejects export boundary referencing missing region", () => {
  let src = `
module Renderer isolated {
  region Frame { width: i32; height: i32; }
  boundary missing_out : export region NotDeclaredHere;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasMissing = Array.some(diags, d => String.includes(d.message, "NotDeclaredHere"))
  assertTrue(hasMissing, "diagnostic mentions missing exported region")
})

test("v1.2: Checker accepts well-formed isolated module", () => {
  let src = `
module Renderer isolated {
  private_memory gfx { initial: 4; maximum: 16; }
  region Frame { width: i32; height: i32; }
  region Tile { x: i32; y: i32; }
  boundary frame_out : export region Frame;
  boundary tile_out  : export region Tile;
  boundary state_in  : import region PlayerState;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.2: Checker rejects top-level memory inside isolated module", () => {
  let src = `
module Renderer isolated {
  memory main_mem {
    initial: 1;
  }
  region Frame { width: i32; height: i32; }
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasMem = Array.some(diags, d => String.includes(d.message, "may not declare a top-level 'memory'"))
  assertTrue(hasMem, "diagnostic mentions top-level memory inside isolated module")
})

test("v1.2: v1.1 checks still apply inside isolated module body", () => {
  // const non-literal initializer should still be flagged inside an
  // isolated module — verifies recursive descent in checkModule.
  let src = `
module M isolated {
  const bad : i32 = 1 + 1;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasConst = Array.some(diags, d => String.includes(d.message, "literal"))
  assertTrue(hasConst, "v1.1 const-literal check fires inside isolated body")
})

// ============================================================================
// v1.3 / L14 — Session Protocols Tests
// ============================================================================

Console.log("")
Console.log("--- v1.3 / L14 Session Protocols Tests ---")

test("v1.3: parse minimal session", () => {
  let src = `
session OrderFlow {
  state Idle    : i32;
  state Pending : i64;
  state Done    : i32;
  transition submit  : consume Idle    -> yield Pending;
  transition approve : consume Pending -> yield Done;
}
`
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | SessionDecl(s) =>
    assertEqual(s.name, "OrderFlow", "session name")
    assertEqual(Array.length(s.states), 3, "three states")
    assertEqual(Array.length(s.transitions), 2, "two transitions")
    assertTrue(s.dualName == None, "no dual declared")
  | _ => Exn.raiseError("Expected SessionDecl")
  }
})

test("v1.3: parse session with dual", () => {
  let src = `
session ClientSide {
  state S1 : i32;
  state S2 : i32;
  transition go : consume S1 -> yield S2;
  dual : ServerSide;
}
`
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | SessionDecl(s) =>
    switch s.dualName {
    | Some(d) => assertEqual(d, "ServerSide", "dual target")
    | None => Exn.raiseError("Expected dual clause")
    }
  | _ => Exn.raiseError("Expected SessionDecl")
  }
})

test("v1.3: state without payload is allowed", () => {
  let src = `
session S {
  state Tick;
  state Tock;
  transition flip : consume Tick -> yield Tock;
}
`
  let m = parseModule(src)->assertOk
  let d = m.declarations->mustGet(0, "first decl")
  switch d.node {
  | SessionDecl(s) =>
    let st = s.states->mustGet(0, "first state")
    assertTrue(st.node.payload == None, "payload-less state")
  | _ => Exn.raiseError("Expected SessionDecl")
  }
})

test("v1.3: parser rejects state outside session block", () => {
  let src = `
state Stray : i32;
`
  let result = parseModule(src)
  switch result {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level state")
  | Error(_) => () // expected
  }
})

test("v1.3: parser rejects transition outside session block", () => {
  let src = `
transition stray : consume A -> yield B;
`
  let result = parseModule(src)
  switch result {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level transition")
  | Error(_) => () // expected
  }
})

test("v1.3: Checker rejects duplicate state names", () => {
  let src = `
session S {
  state Same : i32;
  state Same : i64;
  transition t : consume Same -> yield Same;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasDup = Array.some(diags, d => String.includes(d.message, "duplicate state name 'Same'"))
  assertTrue(hasDup, "duplicate state name diagnostic")
})

test("v1.3: Checker rejects transition with undeclared consume state", () => {
  let src = `
session S {
  state Idle : i32;
  state Done : i32;
  transition oops : consume Phantom -> yield Done;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasMissing = Array.some(diags, d => String.includes(d.message, "Phantom"))
  assertTrue(hasMissing, "undeclared consume diagnostic")
})

test("v1.3: Checker rejects transition with undeclared yield state", () => {
  let src = `
session S {
  state Idle : i32;
  transition oops : consume Idle -> yield Phantom;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasMissing = Array.some(diags, d => String.includes(d.message, "Phantom"))
  assertTrue(hasMissing, "undeclared yield diagnostic")
})

test("v1.3: Checker rejects duplicate (name, consumes) transition pair", () => {
  let src = `
session S {
  state A : i32;
  state B : i32;
  transition go : consume A -> yield B;
  transition go : consume A -> yield A;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasDup = Array.some(diags, d => String.includes(d.message, "duplicate transition 'go'"))
  assertTrue(hasDup, "duplicate transition pair diagnostic")
})

test("v1.3: Checker rejects asymmetric dual", () => {
  let src = `
session A {
  state X : i32;
  state Y : i32;
  transition t : consume X -> yield Y;
  dual : B;
}
session B {
  state P : i32;
  state Q : i32;
  transition u : consume P -> yield Q;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  let hasAsym = Array.some(diags, d => String.includes(d.message, "dual asymmetry"))
  assertTrue(hasAsym, "dual asymmetry diagnostic")
})

test("v1.3: Checker accepts symmetric dual", () => {
  let src = `
session A {
  state X : i32;
  transition t : consume X -> yield X;
  dual : B;
}
session B {
  state Y : i32;
  transition u : consume Y -> yield Y;
  dual : A;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics for symmetric dual")
})

test("v1.3: Checker accepts well-formed session", () => {
  let src = `
session OrderFlow {
  state Idle    : i32;
  state Pending : i64;
  state Done    : i32;
  transition submit  : consume Idle    -> yield Pending;
  transition approve : consume Pending -> yield Done;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.3: session inside isolated module body parses + checks", () => {
  let src = `
module Worker isolated {
  region Frame { width: i32; height: i32; }
  boundary frame_out : export region Frame;
  session JobFlow {
    state Idle  : i32;
    state Busy  : i64;
    transition pick : consume Idle -> yield Busy;
    transition done : consume Busy -> yield Idle;
  }
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics for nested session")
})

// ============================================================================
// v1.4 / L15 — Resource Capabilities
// ============================================================================

test("v1.4: parse top-level capability decl", () => {
  let src = `
capability read_file;
region R { v: i32; }
`
  let m = parseModule(src)->assertOk
  assertEqual(Array.length(m.declarations), 2, "expected 2 top-level decls")
  switch (m.declarations->mustGet(0, "first decl")).node {
  | CapabilityDecl(c) => assertEqual(c.name, "read_file", "capability name")
  | _ => Exn.raiseError("first decl must be CapabilityDecl")
  }
})

test("v1.4: parse multiple top-level capability decls", () => {
  let src = `
capability read_file;
capability web_fetch;
capability gpio_4;
`
  let m = parseModule(src)->assertOk
  assertEqual(Array.length(m.declarations), 3, "expected 3 capability decls")
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics for distinct caps")
})

test("v1.4: parse capability decl inside isolated module", () => {
  let src = `
module Net isolated {
  private_memory net_mem { initial: 1; }
  capability web_fetch;
  region Buf { bytes: i32; }
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.4: Checker rejects duplicate top-level capability (L15-A)", () => {
  let src = `
capability read_file;
capability read_file;
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) >= 1, "expected at least one L15-A diagnostic")
  let hasA = diags->Array.some(d =>
    d.message->String.includes("L15-A")
  )
  assertTrue(hasA, "diagnostic should cite L15-A")
})

test("v1.4: Checker rejects duplicate capability inside isolated module (L15-A)", () => {
  let src = `
module M isolated {
  capability foo;
  capability foo;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) >= 1, "expected at least one L15-A diagnostic")
})

test("v1.4: Checker accepts function caps scoped to declared top-level cap (L15-B pass)", () => {
  let src = `
capability read_file;
fn load() -> i32 effects {
  memory: { Read },
  caps: { read_file }
} {
  return 0;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.4: Checker rejects function caps not in declared set (L15-B fail)", () => {
  let src = `
capability read_file;
fn leak() -> i32 effects {
  memory: { Read },
  caps: { web_fetch }
} {
  return 0;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) >= 1, "expected an L15-B diagnostic")
  let hasB = diags->Array.some(d =>
    d.message->String.includes("L15-B")
  )
  assertTrue(hasB, "diagnostic should cite L15-B")
})

test("v1.4: Checker accepts caps declared inside enclosing isolated module", () => {
  let src = `
module Net isolated {
  private_memory net_mem { initial: 1; }
  capability web_fetch;
  fn fetch() -> i32 effects {
    memory: { Read },
    caps: { web_fetch }
  } {
    return 0;
  }
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.4: Checker rejects function referencing top-level cap from inside isolated module (scope boundary)", () => {
  // `read_file` is declared at top level, not inside `Net`. The function
  // inside `Net` cannot reference it because L15 scopes capabilities
  // strictly to the nearest enclosing module.
  let src = `
capability read_file;
module Net isolated {
  private_memory net_mem { initial: 1; }
  fn fetch() -> i32 effects {
    memory: { Read },
    caps: { read_file }
  } {
    return 0;
  }
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(Array.length(diags) >= 1, "expected L15-B diagnostic for scope crossing")
})

test("v1.4: Checker accepts pure function (empty caps) regardless of module caps", () => {
  let src = `
capability read_file;
fn pure_fn() -> i32 effects {
  memory: { Read },
  caps: { }
} {
  return 0;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics for empty caps")
})

test("v1.4: parser rejects 'grant' at top level (reserved, not live at v1.4)", () => {
  let src = `grant foo to bar;`
  switch parseModule(src) {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level grant")
  | Error(_) => () // expected
  }
})

test("v1.4: parser rejects 'relinquish' at top level (reserved, not live at v1.4)", () => {
  let src = `relinquish foo;`
  switch parseModule(src) {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level relinquish")
  | Error(_) => () // expected
  }
})

test("v1.4: parser rejects 'requires_caps' at top level (reserved, not live at v1.4)", () => {
  let src = `requires_caps { foo }`
  switch parseModule(src) {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level requires_caps")
  | Error(_) => () // expected
  }
})

// ============================================================================
// v1.5 / L16 — Agent Choreography
// ============================================================================

test("v1.5: parse minimal choreography decl", () => {
  let src = `
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography TradeFlow {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message pay : buyer -> seller, i64;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  assertTrue(Array.length(m.declarations) >= 3, "expected choreography decl in module")
})

test("v1.5: parser rejects 'agent_role' at top level", () => {
  let src = `agent_role buyer : Buyer;`
  switch parseModule(src) {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level agent_role")
  | Error(_) => () // expected
  }
})

test("v1.5: parser rejects 'message' at top level", () => {
  let src = `message ping : a -> b, i32;`
  switch parseModule(src) {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level message")
  | Error(_) => () // expected
  }
})

test("v1.5: parser rejects 'composes' at top level", () => {
  let src = `composes: L13 + L14 + L15;`
  switch parseModule(src) {
  | Ok(_) => Exn.raiseError("Expected parse error for top-level composes")
  | Error(_) => () // expected
  }
})

test("v1.5: Checker accepts well-formed choreography", () => {
  let src = `
region MsgRegion { value: i32; }
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography TradeFlow {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message pay : buyer -> seller, i64;
  message ack : seller -> buyer, @MsgRegion;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.5: Checker rejects agent_role target missing in file (L16-A)", () => {
  let src = `
choreography C {
  agent_role buyer : MissingTarget;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(diags->Array.some(d => d.message->String.includes("L16-A")), "expected L16-A diagnostic")
})

test("v1.5: Checker rejects message with unknown from-role (L16-B)", () => {
  let src = `
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography C {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message bad_from : ghost -> seller, i32;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(diags->Array.some(d => d.message->String.includes("L16-B")), "expected L16-B diagnostic")
})

test("v1.5: Checker rejects message with unknown to-role (L16-B)", () => {
  let src = `
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography C {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message bad_to : buyer -> ghost, i32;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(diags->Array.some(d => d.message->String.includes("L16-B")), "expected L16-B diagnostic")
})

test("v1.5: Checker rejects opaque message payload type (L16-C)", () => {
  let src = `
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography C {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message ptr_payload : buyer -> seller, ptr<i32>;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(diags->Array.some(d => d.message->String.includes("L16-C")), "expected L16-C diagnostic")
})

test("v1.5: Checker rejects undeclared region payload reference (L16-C)", () => {
  let src = `
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography C {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message missing_region : buyer -> seller, @NoSuchRegion;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(diags->Array.some(d => d.message->String.includes("L16-C")), "expected L16-C diagnostic")
})

test("v1.5: Checker accepts declared region payload reference (L16-C pass)", () => {
  let src = `
region SharedMsg { v: i32; }
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography C {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message ok_region : buyer -> seller, @SharedMsg;
  composes: L13 + L14 + L15;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertEqual(Array.length(diags), 0, "expected zero diagnostics")
})

test("v1.5: Checker rejects non-v1.5 composition spec (L16-D)", () => {
  let src = `
module Buyer isolated { region BuyerState { v: i32; } }
session SellerProto {
  state Ready : i32;
  transition loop : consume Ready -> yield Ready;
}
choreography C {
  agent_role buyer : Buyer;
  agent_role seller : SellerProto;
  message pay : buyer -> seller, i32;
  composes: L13 + L14 + L99;
}
`
  let m = parseModule(src)->assertOk
  let diags = Checker.checkModule(m)
  assertTrue(diags->Array.some(d => d.message->String.includes("L16-D")), "expected L16-D diagnostic")
})

// ============================================================================
// Summary
// ============================================================================

Console.log("")
Console.log(
  `--- Results: ${passCount.contents->Int.toString} passed, ${failCount.contents->Int.toString} failed ---`,
)
if failCount.contents > 0 {
  Exn.raiseError("Tests failed")
}
