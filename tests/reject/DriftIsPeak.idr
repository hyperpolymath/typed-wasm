-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors occupancy-types
-- tests/reject/DriftIsPeak.agda @ ead4478 (R-6; unchanged since af95728).
--
-- What is live at a cut is not the peak reached before it; identifying them
-- is exactly "an L13 boundary never reclaims anything".
-- EXPECT: Mismatch between: p and n
module DriftIsPeak

import TypedWasm.ABI.ResourceAlgebra.HWM

%default total

invalid : (a : HWMGrade) -> drift a = peak a
invalid (MkHWM p n b) = Refl
