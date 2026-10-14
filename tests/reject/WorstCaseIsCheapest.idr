-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).  typed-wasm's own control.
--
-- L11's worst-case grade (MaxPlus) charges the DEARER branch of a choice.
-- If this were accepted, `Level11WorstCaseProof` would bound the cheapest
-- path, which is what the min-plus Kleene closure already does.
-- EXPECT: Mismatch between: 0 and 1
module WorstCaseIsCheapest

import TypedWasm.ABI.Tropical

%default total

invalid : worstCase (OneOf (Step 2) (Step 3)) = Val 2
invalid = Refl
