-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors resource-algebra
-- tests/reject/HWMAnnihilates.agda @ cf9235c.
--
-- In the high-water-mark algebra the alternatives unit is also the sequence
-- unit, so sequencing with it returns the other grade, not the unit.
-- Accepting this would smuggle an annihilating zero into an algebra that has
-- none (resource-algebra C-4 / H-3).
-- EXPECT: Mismatch between: 0 and n
module HWMAnnihilates

import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

invalid : (g : HWMGrade) -> hwmSeq HWM.hwmZero g = HWM.hwmZero
invalid (MkHWM p n b) = Refl
