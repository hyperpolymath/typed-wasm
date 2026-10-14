-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  L13 occupancy binding.
--
-- An empty run has peak 0, so if only the peak had to fit, every private
-- memory with a declared maximum would be certified, including one declared
-- with `initial` above `maximum` (MkPrivateMemory o n 2 (Just 1)).  The
-- initial allocation is live before any phase runs; WithinMaximum bounds it
-- too.  Before that bound this declaration typechecked (with the first
-- LTEZero dropped).
-- EXPECT: Can't solve constraint between: 0 and pm \.initial
module InitialOverMaximum

import TypedWasm.ABI.ResourceAlgebra
import TypedWasm.ABI.ResourceAlgebra.HWM
import TypedWasm.ABI.ModuleIsolation
import TypedWasm.ABI.Occupancy

%default total

invalid : (pm : PrivateMemory) -> (m : Nat) -> pm.maximum = Just m ->
          WithinMaximum pm (timelineGrade [])
invalid pm m prf = UnderMaximum prf LTEZero LTEZero
