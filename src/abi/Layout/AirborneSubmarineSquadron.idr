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
import Data.List

%default total

public export
snapshotAbiVersion : String
snapshotAbiVersion = "airborne-submarine-squadron.step_state.v1"

public export
snapshotFieldCount : Nat
snapshotFieldCount = 29

public export
inputFieldCount : Nat
inputFieldCount = 5

public export
stepStateArity : Nat
stepStateArity = snapshotFieldCount + inputFieldCount

public export
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

public export
inputFieldNames : List String
inputFieldNames =
  [ "thrust_x"
  , "thrust_y"
  , "fire"
  , "fire_alt"
  , "toggle_env"
  ]

public export
snapshotFieldCountProof
    : length Layout.AirborneSubmarineSquadron.snapshotFieldNames
    = Layout.AirborneSubmarineSquadron.snapshotFieldCount
snapshotFieldCountProof = Refl

public export
inputFieldCountProof
    : length Layout.AirborneSubmarineSquadron.inputFieldNames
    = Layout.AirborneSubmarineSquadron.inputFieldCount
inputFieldCountProof = Refl

public export
snapshotResultHeap : WasmHeapType
snapshotResultHeap = WHT_Array (WVT_Prim WasmI32)

public export
snapshotResultConvention : PassingConvention
snapshotResultConvention = ByRef snapshotResultHeap

public export
i32Convention : PassingConvention
i32Convention = ByValue (WVT_Prim WasmI32)

public export
stepStateParams : List PassingConvention
stepStateParams = replicate stepStateArity i32Convention

public export
stepStateArityProof
    : length Layout.AirborneSubmarineSquadron.stepStateParams
    = Layout.AirborneSubmarineSquadron.stepStateArity
stepStateArityProof = Refl

public export
initStateSig : CrossLangSig
initStateSig = MkCrossLangSig [] [snapshotResultConvention]

public export
stepStateSig : CrossLangSig
stepStateSig = MkCrossLangSig stepStateParams [snapshotResultConvention]

public export
initStateNoParams : params Layout.AirborneSubmarineSquadron.initStateSig = []
initStateNoParams = Refl

public export
stepStateReturnsSnapshot
    : returns Layout.AirborneSubmarineSquadron.stepStateSig
    = [Layout.AirborneSubmarineSquadron.snapshotResultConvention]
stepStateReturnsSnapshot = Refl
