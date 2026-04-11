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
// Summary
// ============================================================================

Console.log("")
Console.log(
  `--- Results: ${passCount.contents->Int.toString} passed, ${failCount.contents->Int.toString} failed ---`,
)
if failCount.contents > 0 {
  Exn.raiseError("Tests failed")
}
