-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors choreographic-types
-- tests/reject/InconsistentCut.agda @ edb784a (K-7).
--
-- The protocol is projectable for party 2 (both branches identical), but
-- the cut truncates the left branch after two messages and the right after
-- one, so the frontier is inconsistent for 2.  Restricted global grade at
-- the cut: Finite 1 (min 2 1); the local timeline cut (left representative)
-- reads Finite 2.  The Consistent side-condition is load-bearing.
-- EXPECT: Mismatch between: S \(plus 0 0\) and 0
module InconsistentCut

import TypedWasm.ABI.KCut
import TypedWasm.ABI.ResourceAlgebra.Loss

%default total

gl : Global LossGrade
gl = Choice 0 1 (Finite 0) (Msg 1 2 (Finite 1) (Msg 1 2 (Finite 1) End))
                           (Msg 1 2 (Finite 1) (Msg 1 2 (Finite 1) End))

c : Cut InconsistentCut.gl
c = ContChoice (ContMsg (ContMsg Stop)) (ContMsg Stop)

invalid : gradeAt 2 (cutGlobal InconsistentCut.gl InconsistentCut.c)
        = lgrade (cutLocal (proj 2 InconsistentCut.gl) (cutproj 2 InconsistentCut.c))
invalid = Refl
