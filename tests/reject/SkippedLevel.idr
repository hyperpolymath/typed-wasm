-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).
--
-- A witness chain that jumps from level 1 to level 3.  `AdvanceW` on a
-- chain at level 1 needs a level-2 witness; a level-3 one does not fit,
-- so a certificate cannot reach a level while skipping the one below it.
-- Idris2 reports the clash of LevelAttestationW 3 with LevelAttestationW 2
-- after peeling the common successors, as 1 against 0.
-- EXPECT: Mismatch between: 1 and 0
module SkippedLevel

import TypedWasm.ABI.Region
import TypedWasm.ABI.MultiModule
import TypedWasm.ABI.Proofs

%default total

invalid : ProgressiveW 2
invalid = AdvanceW (StartW (AttestL1W [])) (AttestL3W (TypeCompat {ty = U8}))
