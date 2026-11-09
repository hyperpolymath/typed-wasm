-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).
--
-- Instance 1 of a region with one instance, certified as in bounds.  The
-- subject-free `AttestL5W` took `zeroInBounds` for any region; here the
-- index and count are the access's own.
-- EXPECT: Mismatch between: S \?right and 0
module CertifiedOutOfBounds

import Data.Nat
import TypedWasm.ABI.Region
import TypedWasm.ABI.TypedAccess
import TypedWasm.ABI.Levels
import TypedWasm.ABI.Pointer
import TypedWasm.ABI.Effects
import TypedWasm.ABI.Lifetime
import TypedWasm.ABI.SessionProtocol
import TypedWasm.ABI.ResourceCapabilities
import TypedWasm.ABI.MultiModule
import TypedWasm.ABI.Certified

%default total

||| One I32 field, "x", read at I32, instance 1 of 1.
subject : Subject
subject = MkSubject [MkField "x" I32] "x" I32 I32 Owning Levels.Static 1 1
                    [] [] Lifetime.Static Lifetime.Static 0 0
                    (MkProtocol (MkSessionId "p") [] [] Nothing) emptyModuleCaps

invalid : Attest CertifiedOutOfBounds.subject 5
invalid = AttS5 (MkInBounds (LTESucc (LTESucc LTEZero)))
