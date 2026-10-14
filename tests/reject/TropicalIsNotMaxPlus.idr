-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  typed-wasm's own control.
--
-- L11's TropCost is the kernel's Loss carrier (min-plus), not MaxPlus: its
-- alternatives keep the CHEAPER branch.  If this were accepted, the reading
-- "Tropical.idr is the MaxPlus instance" would be true, and it is not
-- (LEVEL-STATUS row 11; ResourceAlgebra/Separation.idr S-2).
-- EXPECT: Can't solve constraint between: maximum m n and minimum m n
module TropicalIsNotMaxPlus

import TypedWasm.ABI.Tropical

%default total

invalid : (m, n : Nat) -> tropAdd (Finite m) (Finite n) = Finite (maximum m n)
invalid m n = Refl
