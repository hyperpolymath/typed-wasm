-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors occupancy-types
-- tests/reject/CostIsOccupancy.agda @ af95728 (R-6).
--
-- Occupancy of a sequence is not the sum of the peaks.  Reading it as cost
-- would charge an L13 run for memory its boundary has already reclaimed.
-- EXPECT: Can't solve constraint between: plus .* and maximum p \(n \+ p'\)
module CostIsOccupancy

import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

invalid : (a, c : HWMGrade) -> peak (hwmSeq a c) = peak a + peak c
invalid (MkHWM p n b) (MkHWM p' n' b') = Refl
