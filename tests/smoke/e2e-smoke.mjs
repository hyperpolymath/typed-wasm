// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// End-to-end smoke test for typed-wasm P0 validation.
//
// This script:
//   1. Reads examples/01-single-module.twasm
//   2. Parses it with the ReScript parser
//   3. Extracts region schemas from the AST
//   4. Verifies the schema structure matches what the Idris2 ABI types expect
//
// Run: node tests/smoke/e2e-smoke.mjs

import { readFileSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { parseModule } from "../../src/parser/Parser.mjs";

const __dirname = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(__dirname, "../..");

let passed = 0;
let failed = 0;

function assert(condition, message) {
  if (condition) {
    console.log(`  OK: ${message}`);
    passed++;
  } else {
    console.error(`  FAIL: ${message}`);
    failed++;
  }
}

// ============================================================================
// Step 1: Read example file
// ============================================================================

console.log("=== E2E Smoke Test: typed-wasm P0 ===\n");
console.log("Step 1: Read examples/01-single-module.twasm");

const examplePath = resolve(projectRoot, "examples/01-single-module.twasm");
const source = readFileSync(examplePath, "utf-8");
assert(source.length > 0, "File is non-empty");
assert(source.includes("region Vec2"), "File contains Vec2 region");
assert(source.includes("region Players"), "File contains Players region");

// ============================================================================
// Step 2: Parse with ReScript parser
// ============================================================================

console.log("\nStep 2: Parse with ReScript parser");

const result = parseModule(source);
assert(result.TAG === "Ok", "Parse succeeds without errors");

const module_ = result._0;
const declarations = module_.declarations;
assert(declarations.length >= 8, `Has >= 8 declarations (got ${declarations.length})`);

// ============================================================================
// Step 3: Extract region schemas from AST
// ============================================================================

console.log("\nStep 3: Extract region schemas from AST");

// Extract all region declarations
const regions = [];
const functions = [];
const memories = [];

for (const decl of declarations) {
  const node = decl.node;
  if (typeof node === "object" && node.TAG === "RegionDecl") {
    regions.push(node._0);
  } else if (typeof node === "object" && node.TAG === "FunctionDecl") {
    functions.push(node._0);
  } else if (typeof node === "object" && node.TAG === "MemoryDecl") {
    memories.push(node._0);
  }
}

assert(regions.length >= 3, `Has >= 3 region declarations (got ${regions.length})`);
assert(functions.length >= 4, `Has >= 4 function declarations (got ${functions.length})`);
assert(memories.length >= 1, `Has >= 1 memory declaration (got ${memories.length})`);

// ============================================================================
// Step 4: Verify schema structure against Idris2 ABI expectations
// ============================================================================

console.log("\nStep 4: Verify schema structure against Idris2 ABI expectations");

// Find specific regions by name
const vec2Region = regions.find((r) => r.name === "Vec2");
const playersRegion = regions.find((r) => r.name === "Players");
const enemiesRegion = regions.find((r) => r.name === "Enemies");

// --- Vec2 region ---
assert(vec2Region !== undefined, "Vec2 region found");
assert(vec2Region.fields.length === 2, `Vec2 has 2 fields (got ${vec2Region.fields.length})`);
assert(
  vec2Region.fields[0].node.name === "x",
  `Vec2 field 0 is 'x' (got '${vec2Region.fields[0].node.name}')`
);
assert(
  vec2Region.fields[1].node.name === "y",
  `Vec2 field 1 is 'y' (got '${vec2Region.fields[1].node.name}')`
);

// Verify field types are f32 (Primitive with tag "F32")
// The AST represents Primitive(F32) as { TAG: "Primitive", _0: "F32" }
const vec2F0Type = vec2Region.fields[0].node.fieldType.node;
const vec2F1Type = vec2Region.fields[1].node.fieldType.node;
assert(
  vec2F0Type.TAG === "Primitive" && vec2F0Type._0 === "F32",
  `Vec2.x is f32 (got ${JSON.stringify(vec2F0Type)})`
);
assert(
  vec2F1Type.TAG === "Primitive" && vec2F1Type._0 === "F32",
  `Vec2.y is f32 (got ${JSON.stringify(vec2F1Type)})`
);

// No instance count for Vec2 (singleton)
assert(
  vec2Region.instanceCount === undefined,
  "Vec2 has no instance count (singleton region)"
);

// --- Players region ---
assert(playersRegion !== undefined, "Players region found");
assert(
  playersRegion.instanceCount !== undefined,
  "Players has instance count (array region)"
);
assert(
  playersRegion.fields.length >= 4,
  `Players has >= 4 fields (got ${playersRegion.fields.length})`
);

// Players field types match Idris2 ABI WasmType expectations:
// hp: i32 (ABI: I32, size 4)
// speed: f64 (ABI: F64, size 8)
// pos: @Vec2 (ABI: RegionRef, embedded)
// name: u8[24] (ABI: ArrayFieldType of U8)
const hpField = playersRegion.fields.find((f) => f.node.name === "hp");
assert(hpField !== undefined, "Players.hp field exists");
assert(
  hpField.node.fieldType.node.TAG === "Primitive" &&
    hpField.node.fieldType.node._0 === "I32",
  `Players.hp is i32 (matches ABI WasmType.I32)`
);

const speedField = playersRegion.fields.find((f) => f.node.name === "speed");
assert(speedField !== undefined, "Players.speed field exists");
assert(
  speedField.node.fieldType.node.TAG === "Primitive" &&
    speedField.node.fieldType.node._0 === "F64",
  `Players.speed is f64 (matches ABI WasmType.F64)`
);

const posField = playersRegion.fields.find((f) => f.node.name === "pos");
assert(posField !== undefined, "Players.pos field exists");
assert(
  posField.node.fieldType.node.TAG === "RegionRef" &&
    posField.node.fieldType.node._0 === "Vec2",
  `Players.pos is @Vec2 (embedded region reference)`
);

const nameField = playersRegion.fields.find((f) => f.node.name === "name");
assert(nameField !== undefined, "Players.name field exists");
assert(
  nameField.node.fieldType.node.TAG === "ArrayFieldType",
  `Players.name is an array type (u8[24])`
);

// Players has alignment
assert(
  playersRegion.alignment !== undefined,
  "Players has alignment specified"
);

// --- Enemies region ---
assert(enemiesRegion !== undefined, "Enemies region found");
assert(
  enemiesRegion.instanceCount !== undefined,
  "Enemies has instance count"
);

// Check nullable field: target: opt<@Players>
const targetField = enemiesRegion.fields.find((f) => f.node.name === "target");
assert(targetField !== undefined, "Enemies.target field exists");
assert(
  targetField.node.fieldType.node.TAG === "OptionalType",
  `Enemies.target is opt<...> (Level 4: null safety)`
);

// --- Memory declaration ---
const gameMem = memories.find((m) => m.name === "game_memory");
assert(gameMem !== undefined, "game_memory declaration found");
assert(gameMem.initialPages > 0, `game_memory has initial pages (${gameMem.initialPages})`);
assert(
  gameMem.maximumPages !== undefined,
  "game_memory has maximum pages"
);
assert(
  gameMem.placements.length >= 2,
  `game_memory has >= 2 placements (got ${gameMem.placements.length})`
);

// --- Functions ---
const getHpFn = functions.find((f) => f.name === "get_player_hp");
assert(getHpFn !== undefined, "get_player_hp function found");
assert(getHpFn.params.length === 2, `get_player_hp has 2 params`);
assert(getHpFn.returnType !== undefined, "get_player_hp has return type");
assert(
  getHpFn.effects !== undefined && getHpFn.effects.length >= 1,
  `get_player_hp has effects declared`
);

// Verify region handle parameter type
const playersParam = getHpFn.params[0];
assert(
  playersParam.node.paramType.node.TAG === "RegionHandleParam",
  `First param is a region handle (matches ABI Region type)`
);

// ============================================================================
// ABI Correspondence Summary
// ============================================================================

console.log("\nABI Correspondence Summary:");
console.log("  Parser AST      | Idris2 ABI Type");
console.log("  ────────────────┼─────────────────────");
console.log("  Primitive(I32)  | WasmType.I32 (size 4)");
console.log("  Primitive(F32)  | WasmType.F32 (size 4)");
console.log("  Primitive(F64)  | WasmType.F64 (size 8)");
console.log("  RegionRef(name) | Region schema (embedded)");
console.log("  OptionalType    | Nullable field (Level 4)");
console.log("  ArrayFieldType  | Fixed-size array");
console.log("  instanceCount   | Region.count");
console.log("  alignment       | Schema alignment");

// ============================================================================
// Summary
// ============================================================================

console.log(`\n=== Results: ${passed} passed, ${failed} failed ===`);

if (failed > 0) {
  process.exit(1);
}
