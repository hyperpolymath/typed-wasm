-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors choreographic-types
-- tests/reject/UnprojectableChoice.agda @ edb784a (K-7).
--
-- Party 2 is outside the choice 0 → 1, and the two branches project to
-- different local types for it (recv at loss 2 vs recv at loss 1).  Plain
-- merge fails, and the equality K-CUT-LOSS promises is false: restricted
-- global grade Finite 1 (min of the branches), local grade Finite 2 (the
-- left representative).  The Projectable side-condition is load-bearing.
-- EXPECT: Mismatch between: S \(plus 0 0\) and 0
module UnprojectableChoice

import TypedWasm.ABI.KCut
import TypedWasm.ABI.ResourceAlgebra.Loss

%default total

gl : Global LossGrade
gl = Choice 0 1 (Finite 0) (Msg 1 2 (Finite 2) End) (Msg 1 2 (Finite 1) End)

invalid : gradeAt 2 UnprojectableChoice.gl = lgrade (proj 2 UnprojectableChoice.gl)
invalid = Refl
