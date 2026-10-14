-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors resource-algebra
-- tests/reject/LossWorstCase.agda @ cf9235c.
--
-- Echo's alternatives are MIN (the less lossy branch), not MAX.  Reading them
-- as worst-case would identify the loss grade with a cost grade.
-- EXPECT: Can't solve constraint between: maximum m n and minimum m n
module LossWorstCase

import TypedWasm.ABI.ResourceAlgebra.Loss

%default total

invalid : (m, n : Nat) -> lossAlt (Finite m) (Finite n) = Finite (maximum m n)
invalid m n = Refl
