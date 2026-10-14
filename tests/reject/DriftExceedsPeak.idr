-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors resource-algebra
-- tests/reject/DriftExceedsPeak.agda @ cf9235c.
--
-- A run cannot end holding more live state than its peak.  The invariant is
-- a field of the grade, so no such grade can be written down.
-- EXPECT: Mismatch between: S \?right and 0
module DriftExceedsPeak

import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

invalid : HWMGrade
invalid = MkHWM 1 2 (LTESucc (LTESucc LTEZero))
