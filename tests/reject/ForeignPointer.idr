-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL (tools/check-kernel-proofs.sh).
--
-- A non-null pointer into a different region (one F32 field "y") offered as
-- the L4 witness for an access to the region with the I32 field "x".  The
-- subject-free `AttestL4W` took a pointer into any schema.
-- EXPECT: Mismatch between: F32 and I32
module ForeignPointer

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

||| One I32 field, "x", read at I32, instance 0 of 1.
subject : Subject
subject = MkSubject [MkField "x" I32] "x" I32 I32 Owning Levels.Static 0 1
                    [] [] Lifetime.Static Lifetime.Static 0 0
                    (MkProtocol (MkSessionId "p") [] [] Nothing) emptyModuleCaps

||| A pointer into another region.
other : Pointer.Ptr Owning [MkField "y" F32] Levels.Static NonNull
other = MkPtr 64

invalid : Attest ForeignPointer.subject 4
invalid = AttS4 other
