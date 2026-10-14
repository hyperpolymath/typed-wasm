-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Explore.idr — the EXPLORER side of the transcription check.
--
-- Evaluates the Idris2 kernel's operations on a fixed finite domain and prints
-- one TSV row per (instance, operation, left, right):
--     <instance> TAB <op> TAB <left> TAB <right> TAB <result>
-- tests/transcription/gen.sh renders those rows into an Agda module that the
-- pinned resource-algebra sources must accept by `refl`, and into an Idris2
-- module this port must accept by `Refl`.  If the port and the Agda source
-- disagree on any tabled input, the Agda side refuses.
--
-- Domain: Loss {fin 0..3, inf}, MaxPlus {val 0..3, bot} (every clause of
-- every operation is reached), HWM {(p, n) | n <= p <= 2}.
module Main

import Data.List
import TypedWasm.ABI.ResourceAlgebra.Loss
import TypedWasm.ABI.ResourceAlgebra.MaxPlus
import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

showL : LossGrade -> String
showL (Finite n) = "fin " ++ show n
showL Infinity   = "inf"

showM : MaxPlusGrade -> String
showM (Val n) = "val " ++ show n
showM Bot     = "bot"

showH : HWMGrade -> String
showH g = "hwm " ++ show g.peak ++ " " ++ show g.drift

lossDom : List LossGrade
lossDom = [Finite 0, Finite 1, Finite 2, Finite 3, Infinity]

maxDom : List MaxPlusGrade
maxDom = [Val 0, Val 1, Val 2, Val 3, Bot]

hwmDom : List HWMGrade
hwmDom =
  [ MkHWM 0 0 LTEZero, MkHWM 1 0 LTEZero, MkHWM 1 1 (LTESucc LTEZero)
  , MkHWM 2 0 LTEZero, MkHWM 2 1 (LTESucc LTEZero)
  , MkHWM 2 2 (LTESucc (LTESucc LTEZero)) ]

rows : String -> String -> (a -> String) -> (a -> a -> a) -> List a -> List String
rows inst op sh f dom =
  [ inst ++ "\t" ++ op ++ "\t" ++ sh x ++ "\t" ++ sh y ++ "\t" ++ sh (f x y)
  | x <- dom, y <- dom ]

main : IO ()
main = traverse_ putStrLn $
     rows "Loss"    "alt" showL lossAlt    lossDom
  ++ rows "Loss"    "seq" showL lossSeq    lossDom
  ++ rows "MaxPlus" "alt" showM maxPlusAlt maxDom
  ++ rows "MaxPlus" "seq" showM maxPlusSeq maxDom
  ++ rows "HWM"     "alt" showH hwmAlt     hwmDom
  ++ rows "HWM"     "seq" showH hwmSeq     hwmDom
