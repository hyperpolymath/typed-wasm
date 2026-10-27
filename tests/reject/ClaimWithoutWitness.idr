-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).
--
-- A witness certificate that sets its highest level to 7 but holds no
-- attestations.  `WitnessAchieved` reads the attestations, not the
-- highest-level field, so the claim has nothing to point at.
-- EXPECT: Mismatch between: MkAttestation \?n Proven :: \?rest and \[\]
module ClaimWithoutWitness

import TypedWasm.ABI.MultiModule
import TypedWasm.ABI.Proofs

%default total

invalid : WitnessAchieved 7 (MkWitnessCert [] 7 [])
invalid = LAHere
