-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- src/abi/layout/AirborneSubmarineSquadron.idr
--
-- Versioned JS↔WASM snapshot ABI contract for Airborne Submarine Squadron.
-- This pins the step_state call shape used by the Gossamer runtime:
--
--   init_state()                        -> ptr<i32> snapshot array
--   step_state(29 state i32s + 5 input i32s) -> ptr<i32> snapshot array
--
-- Snapshot ownership stays in the game/Gossamer loop. Burble may consume
-- mirrored events over Groove/API/FFI, but does not own gameplay event state.

module Layout.AirborneSubmarineSquadron

import Layout.Types
import Layout.ABI

%default total

snapshotAbiVersion : String
snapshotAbiVersion = "airborne-submarine-squadron.step_state.v1"

snapshotFieldCount : Nat
snapshotFieldCount = 29

inputFieldCount : Nat
inputFieldCount = 5

stepStateArity : Nat
stepStateArity = snapshotFieldCount + inputFieldCount

snapshotFieldNames : List String
snapshotFieldNames =
  [ "tick"
  , "env"
  , "sub_x"
  , "sub_y"
  , "sub_vx"
  , "sub_vy"
  , "sub_hp"
  , "sub_ammo"
  , "sub_cooldown"
  , "proj_a_alive"
  , "proj_a_x"
  , "proj_a_y"
  , "proj_b_alive"
  , "proj_b_x"
  , "proj_b_y"
  , "enemy1_alive"
  , "enemy1_x"
  , "enemy1_y"
  , "enemy1_hp"
  , "enemy2_alive"
  , "enemy2_x"
  , "enemy2_y"
  , "enemy2_hp"
  , "score"
  , "kills"
  , "mission_total"
  , "mission_ticks"
  , "mission_complete"
  , "mission_failed"
  ]

inputFieldNames : List String
inputFieldNames =
  [ "thrust_x"
  , "thrust_y"
  , "fire"
  , "fire_alt"
  , "toggle_env"
  ]

snapshotFieldCountProof : length snapshotFieldNames = snapshotFieldCount
snapshotFieldCountProof = Refl

inputFieldCountProof : length inputFieldNames = inputFieldCount
inputFieldCountProof = Refl

snapshotResultHeap : WasmHeapType
snapshotResultHeap = WHT_Array (WVT_Prim WasmI32)

snapshotResultConvention : PassingConvention
snapshotResultConvention = ByRef snapshotResultHeap

i32Convention : PassingConvention
i32Convention = ByValue (WVT_Prim WasmI32)

stepStateParams : List PassingConvention
stepStateParams = replicate stepStateArity i32Convention

stepStateArityProof : length stepStateParams = stepStateArity
stepStateArityProof = Refl

initStateSig : CrossLangSig
initStateSig = MkCrossLangSig [] [snapshotResultConvention]

stepStateSig : CrossLangSig
stepStateSig = MkCrossLangSig stepStateParams [snapshotResultConvention]

initStateNoParams : params initStateSig = []
initStateNoParams = Refl

stepStateReturnsSnapshot : returns stepStateSig = [snapshotResultConvention]
stepStateReturnsSnapshot = Refl
