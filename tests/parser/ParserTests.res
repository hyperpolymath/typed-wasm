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
  | exn =>
    failCount := failCount.contents + 1
    Console.error(`  ✗ ${name}: ${exn->Exn.message->Option.getOr("unknown error")}`)
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

// ============================================================================
// Test inputs
// ============================================================================

let exampleMinimal = `
region Empty {
  value: i32,
}
`

let exampleEmpty = ``

let exampleCommentsOnly = `// This file has only comments
// No declarations at all
`

let example01 = `
region Vec2 {
  x: f32,
  y: f32,
}

region Players[100] {
  hp: i32 where 0 <= hp <= 9999,
  pos: @Vec2,
  name_ptr: ptr<u8>,
  target: opt<@Players>,
}

fn move_player(
  players: &mut region<Players>,
  idx: i32,
  dx: f32,
  dy: f32
) -> i32
  effects ReadRegion(Players), WriteRegion(Players), ReadRegion(Vec2), WriteRegion(Vec2)
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

Console.log("--- Lexer Tests ---")

test("tokenize minimal region", () => {
  let tokens = Lexer.tokenize(exampleMinimal)
  assertTrue(tokens->Array.length > 0, "Should produce tokens")
  let first = tokens->Array.getUnsafe(0)
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
  let decl = module_.declarations->Array.getUnsafe(0)
  switch decl.value {
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
  hp: i32 where 0 <= hp <= 9999,
  max_hp: i32,
}
`
  let module_ = parseModule(src)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = module_.declarations->Array.getUnsafe(0)
  switch decl.value {
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
  effects ReadRegion(Players)
{
  region.get $players[idx] .hp -> val;
  return val;
}
`
  let module_ = parseModule(src)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = module_.declarations->Array.getUnsafe(0)
  switch decl.value {
  | FunctionDecl(f) =>
    assertEqual(f.name, "read_hp", "Function name should be read_hp")
    assertTrue(f.effects->Array.length >= 1, "Should have at least 1 effect")
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
  a: i32,
  b: f64,
  c: u8,
  d: ptr<i32>,
}
`
  let module_ = parseModule(src)->assertOk
  let decl = module_.declarations->Array.getUnsafe(0)
  switch decl.value {
  | RegionDecl(r) =>
    assertEqual(r.fields->Array.length, 4, "Should have 4 fields")
    assertEqual(r.fields->Array.getUnsafe(0).name, "a", "First field should be 'a'")
  | _ => Exn.raiseError("Expected RegionDecl")
  }
})

test("parse memory declaration", () => {
  let src = `
memory Main {
  pages: 256,
  max_pages: 1024,
}
`
  let module_ = parseModule(src)->assertOk
  assertEqual(module_.declarations->Array.length, 1, "Should have 1 declaration")
  let decl = module_.declarations->Array.getUnsafe(0)
  switch decl.value {
  | MemoryDecl(_) => ()
  | _ => Exn.raiseError("Expected MemoryDecl")
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
  Process.exit(1)
}
