// SPDX-License-Identifier: PMPL-1.0-or-later
// Contract test: Airborne Submarine Squadron JS↔WASM snapshot ABI (v1)

import { existsSync, readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = dirname(fileURLToPath(import.meta.url));
const projectRoot = resolve(__dirname, "../..");
const contractPath = resolve(
  projectRoot,
  "src/contracts/airborne-submarine-squadron.snapshot-abi.v1.json",
);

let passed = 0;
let failed = 0;

function assert(condition, message) {
  if (condition) {
    passed += 1;
    console.log(`  OK: ${message}`);
    return;
  }
  failed += 1;
  console.error(`  FAIL: ${message}`);
}

function finish() {
  console.log(`\nResults: ${passed} passed, ${failed} failed`);
  if (failed > 0) process.exit(1);
}

function findFirstExisting(paths) {
  for (const path of paths) {
    if (existsSync(path)) return path;
  }
  return null;
}

console.log("=== Contract Test: Airborne step_state ABI v1 ===\n");

const contract = JSON.parse(readFileSync(contractPath, "utf-8"));

// ---------------------------------------------------------------------------
// 1) Static contract shape checks
// ---------------------------------------------------------------------------
assert(contract.id === "airborne-submarine-squadron.step_state.snapshot", "contract id is stable");
assert(contract.version === "1.0.0", "contract version is 1.0.0");

assert(contract.snapshot.state_field_count === 29, "snapshot field count is 29");
assert(contract.input.field_count === 5, "input field count is 5");
assert(
  contract.exports.step_state.params.length ===
    contract.snapshot.state_field_count + contract.input.field_count,
  "step_state parameter count is snapshot+input (34)",
);

assert(contract.exports.init_state.params.length === 0, "init_state has no params");
assert(contract.exports.init_state.result === "ptr<i32>", "init_state result is ptr<i32>");
assert(contract.exports.step_state.result === "ptr<i32>", "step_state result is ptr<i32>");

assert(
  contract.snapshot.fields[contract.snapshot.indexes.tick] === "tick",
  "tick index maps to tick",
);
assert(
  contract.snapshot.fields[contract.snapshot.indexes.score] === "score",
  "score index maps to score",
);
assert(
  contract.snapshot.fields[contract.snapshot.indexes.kills] === "kills",
  "kills index maps to kills",
);

const stateParams = contract.exports.step_state.params.slice(0, contract.snapshot.state_field_count);
const inputParams = contract.exports.step_state.params.slice(contract.snapshot.state_field_count);
assert(stateParams.every((name) => name.startsWith("state_")), "first 29 step_state params are state_*");
assert(inputParams.every((name) => name.startsWith("input_")), "last 5 step_state params are input_*");
assert(
  inputParams.join(",") ===
    "input_thrust_x,input_thrust_y,input_fire,input_fire_alt,input_toggle_env",
  "input params order is canonical",
);

// ---------------------------------------------------------------------------
// 2) Optional dogfood check against airborne repo artifact/source
// ---------------------------------------------------------------------------
const airborneRoot = findFirstExisting([
  resolve(projectRoot, "../../games-ecosystem/airborne-submarine-squadron"),
  "/var/mnt/eclipse/repos/games-ecosystem/airborne-submarine-squadron",
]);

if (airborneRoot) {
  console.log("\nDogfood check: validating against airborne repo");
  const wasmPath = resolve(airborneRoot, "dist/airborne-submarine-squadron.wasm");
  const appPath = resolve(airborneRoot, "gossamer/app_gossamer.js");

  if (!existsSync(wasmPath)) {
    assert(false, `airborne wasm artifact exists (${wasmPath})`);
  } else {
    const bytes = readFileSync(wasmPath);
    const { instance } = await WebAssembly.instantiate(bytes, {
      wasi_snapshot_preview1: { fd_write: () => 0 },
    });
    const { init_state, step_state, memory } = instance.exports;
    assert(typeof init_state === "function", "wasm exports init_state");
    assert(typeof step_state === "function", "wasm exports step_state");
    assert(init_state.length === contract.exports.init_state.params.length, "init_state arity matches contract");
    assert(step_state.length === contract.exports.step_state.params.length, "step_state arity matches contract");

    const view = new DataView(memory.buffer);
    const readSnapshot = (ptr) => {
      const tag = view.getInt32(ptr, true);
      const len = view.getInt32(ptr + 4, true);
      const payload = [];
      for (let i = 0; i < len; i += 1) {
        payload.push(view.getInt32(ptr + 8 + i * 4, true));
      }
      return { tag, len, payload };
    };

    const initSnap = readSnapshot(init_state());
    assert(initSnap.len === contract.snapshot.state_field_count, "init_state payload length matches contract (29)");
    assert(initSnap.payload.length === contract.snapshot.state_field_count, "init_state payload reads 29 fields");

    const stepped = readSnapshot(
      step_state(...initSnap.payload, 0, 0, 0, 0, 0),
    );
    assert(stepped.len === contract.snapshot.state_field_count, "step_state payload length matches contract (29)");
    assert(stepped.payload.length === contract.snapshot.state_field_count, "step_state payload reads 29 fields");
    assert(typeof stepped.payload[contract.snapshot.indexes.tick] === "number", "tick slot is numeric");
    assert(typeof stepped.payload[contract.snapshot.indexes.score] === "number", "score slot is numeric");
    assert(typeof stepped.payload[contract.snapshot.indexes.kills] === "number", "kills slot is numeric");
  }

  if (!existsSync(appPath)) {
    assert(false, `airborne JS bridge source exists (${appPath})`);
  } else {
    const app = readFileSync(appPath, "utf-8");
    assert(app.includes("world.wasmScore  = world.wasmState[23]"), "JS bridge uses score index 23");
    assert(app.includes("world.wasmKills  = world.wasmState[24]"), "JS bridge uses kills index 24");
  }
} else {
  console.log("\nDogfood check skipped: airborne repo not found on this machine.");
}

finish();
