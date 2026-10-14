-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  Mirrors resource-algebra
-- tests/reject/MinMaxIsLoss.agda @ 0b338c9.
--
-- The bottleneck sequence keeps the worst hop; it does not add the hops.
-- Accepting this would let a min-max bound (L11's Level11BottleneckProof) be
-- read as a min-plus (loss) bound, the identification Separation S-4 and
-- upstream's lax (not strict) loss-bottleneck morphism exist to forbid.
-- EXPECT: Can.t solve constraint between: plus m n and maximum m n
module MinMaxIsLoss

import TypedWasm.ABI.ResourceAlgebra.MinMax

%default total

invalid : (m, n : Nat) -> minMaxSeq (Finite m) (Finite n) = Finite (m + n)
invalid m n = Refl
