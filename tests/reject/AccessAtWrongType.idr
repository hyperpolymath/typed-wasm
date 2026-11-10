-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).
--
-- An access that reads the I32 field "x" at F64.  Its L3 attestation must
-- relate the field's declared type to the access type; the subject-free
-- `AttestL3W` accepted `TypeCompat` at any one type, so a chain could carry
-- L3 for a read at the wrong width.
-- EXPECT: Mismatch between: F64 and I32
module AccessAtWrongType

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

||| One I32 field, "x", read at F64, instance 0 of 1.
subject : Subject
subject = MkSubject [MkField "x" I32] "x" I32 F64 Owning Levels.Static 0 1
                    [] [] Lifetime.Static Lifetime.Static 0 0
                    (MkProtocol (MkSessionId "p") [] [] Nothing) emptyModuleCaps

invalid : Attest AccessAtWrongType.subject 3
invalid = AttS3 TypeCompat
