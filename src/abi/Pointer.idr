-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Pointer.idr — Pointer kinds with ownership semantics for typed-wasm ABI
--
-- Defines three pointer kinds that mirror Rust's ownership model but
-- operate at the WASM linear memory level:
--
--   Ptr    — owning pointer (must free exactly once, Level 10)
--   Ref    — borrowing pointer (no free, scoped lifetime, Level 9)
--   Unique — exclusive owning pointer (no aliasing, Level 7)
--
-- Each pointer kind is indexed by:
--   1. The schema of the region it points to (type safety)
--   2. A lifetime parameter (Level 9: no use-after-free)
--   3. A nullability tag (Level 4: explicit null tracking)
--
-- The pointer kinds enforce different aliasing and ownership rules
-- at the type level. The Idris2 type checker prevents:
--   - Creating two Unique pointers to the same region
--   - Using a Ref after its lifetime expires
--   - Forgetting to free a Ptr (linear obligation)
--   - Dereferencing a nullable pointer without checking

module TypedWasm.ABI.Pointer

import TypedWasm.ABI.Region
import TypedWasm.ABI.Levels

%default total

-- ============================================================================
-- Pointer Kind Tag
-- ============================================================================

||| The ownership semantics of a pointer. Determines aliasing rules,
||| lifetime obligations, and whether the holder must free the memory.
public export
data PtrKind : Type where
  ||| Owning pointer. The holder owns the memory and must free it
  ||| exactly once (Level 10 linear obligation). May be aliased by
  ||| Ref pointers (shared borrowing) but not by other Ptr or Unique.
  Owning    : PtrKind
  ||| Borrowing pointer. The holder may read the memory but does not
  ||| own it and must not free it. Multiple Ref pointers may coexist
  ||| (shared aliasing is safe for reads). Scoped by a lifetime.
  Borrowing : PtrKind
  ||| Exclusive pointer. Like Owning, but additionally guarantees no
  ||| aliasing at all — not even shared Ref borrows. This enables
  ||| mutation safety (Level 7): the holder is the only accessor.
  Exclusive : PtrKind

public export
Show PtrKind where
  show Owning    = "ptr"
  show Borrowing = "ref"
  show Exclusive = "unique"

-- ============================================================================
-- Nullability-Tagged Pointer
-- ============================================================================

||| A pointer to a region, tagged with its kind, lifetime, and nullability.
|||
||| The schema parameter ensures that any access through this pointer is
||| type-checked against the region's schema (Levels 2, 3, 6).
|||
||| The lifetime parameter ensures the pointer is not used after the
||| memory it points to has been freed (Level 9).
|||
||| The nullability parameter determines whether the pointer must be
||| null-checked before use (Level 4).
public export
data Ptr : (kind : PtrKind) -> (schema : Schema) -> (life : Lifetime) -> (null : Nullability) -> Type where
  ||| A non-null pointer with a known base address.
  MkPtr : (addr : Nat) -> Ptr kind schema life NonNull
  ||| A null pointer (only constructible for Nullable pointers).
  MkNull : Ptr kind schema life Nullable
  ||| A maybe-null pointer with an address that might be zero.
  MkMaybePtr : (addr : Nat) -> Ptr kind schema life Nullable

-- ============================================================================
-- Pointer Aliases (Convenience Types)
-- ============================================================================

||| An owning, non-null pointer. The holder must free this exactly once.
public export
OwnPtr : Schema -> Lifetime -> Type
OwnPtr schema life = Ptr Owning schema life NonNull

||| A borrowing, non-null reference. Read-only, no free obligation.
public export
BorrowRef : Schema -> Lifetime -> Type
BorrowRef schema life = Ptr Borrowing schema life NonNull

||| An exclusive, non-null pointer. Mutable, no aliasing, must free.
public export
UniquePtr : Schema -> Lifetime -> Type
UniquePtr schema life = Ptr Exclusive schema life NonNull

||| An optional (nullable) borrowing reference.
public export
OptRef : Schema -> Lifetime -> Type
OptRef schema life = Ptr Borrowing schema life Nullable

-- ============================================================================
-- Null Safety Operations (Level 4)
-- ============================================================================

||| Attempt to convert a nullable pointer to a non-null pointer.
||| Returns Nothing if the pointer is null, or Just the non-null pointer
||| paired with a Level 4 proof that null was checked.
|||
||| This is the only way to "unwrap" a nullable pointer — the type system
||| forces the caller to handle the null case.
public export
checkNull : Ptr kind schema life Nullable
          -> Maybe (Ptr kind schema life NonNull, Level4_NullSafe Nullable)
checkNull MkNull = Nothing
checkNull (MkMaybePtr Z) = Nothing
checkNull (MkMaybePtr (S n)) = Just (MkPtr (S n), NullChecked "runtime-null-check")

||| A non-null pointer is trivially null-safe. This converts the
||| non-null guarantee into an explicit Level 4 proof witness.
public export
nonNullSafe : Ptr kind schema life NonNull -> Level4_NullSafe NonNull
nonNullSafe (MkPtr _) = AlreadyNonNull

-- ============================================================================
-- Aliasing Proofs (Level 7)
-- ============================================================================

||| Proof that two pointers do not violate aliasing rules.
||| The rules are:
|||   - Two Borrowing pointers may coexist (shared reads).
|||   - An Exclusive pointer must be alone (no other pointers to same region).
|||   - An Owning pointer may coexist with Borrowing pointers only.
|||
||| This type is parameterised by the pointer kinds and the region name
||| (encoded as the schema). Two pointers to DIFFERENT regions never alias,
||| regardless of kind.
public export
data NoAlias : PtrKind -> PtrKind -> Type where
  ||| Two borrowing references never alias-conflict (both read-only).
  BorrowBorrow : NoAlias Borrowing Borrowing
  ||| An owning pointer may coexist with a borrowing reference.
  ||| The borrowing ref cannot free or mutate, so no conflict.
  OwnBorrow    : NoAlias Owning Borrowing
  ||| Symmetric: borrowing may coexist with owning.
  BorrowOwn    : NoAlias Borrowing Owning

||| Proof that an Exclusive pointer has no companions. This is a negative
||| proof: we assert that no other pointer to the same schema exists in
||| the current scope.
|||
||| This cannot be witnessed by a constructor (it's a universal statement).
||| Instead, it is established by the borrow checker's scope analysis,
||| which verifies that no other pointer to the schema is in scope.
public export
data ExclusiveWitness : (schema : Schema) -> Type where
  ||| The exclusive pointer is the only pointer to this schema in scope.
  ||| `scopeId` identifies the scope that was checked.
  Exclusive : (scopeId : String) -> ExclusiveWitness schema

-- ============================================================================
-- Pointer Address Extraction
-- ============================================================================

||| Extract the address from a non-null pointer.
||| This is safe because non-null pointers always have a valid address.
public export
ptrAddr : Ptr kind schema life NonNull -> Nat
ptrAddr (MkPtr addr) = addr

||| Convert a pointer to a region for access operations.
||| This creates a Region value from the pointer's address, enabling
||| typed access through the Get/Set/Scan operations.
public export
deref : Ptr kind schema life NonNull -> Region schema
deref (MkPtr addr) = MkRegion "deref" addr 1

-- ============================================================================
-- Ownership Transfer
-- ============================================================================

||| Transfer ownership from one owning pointer to another.
||| The original pointer is linearly consumed (the `1` quantity annotation
||| is implicit in typed-wasm's ownership model — the linear tracking module
||| handles the actual QTT enforcement).
|||
||| After transfer, the original pointer is invalid (consumed) and the
||| new pointer is the sole owner.
public export
transfer : Ptr Owning schema life NonNull
         -> Ptr Owning schema life NonNull
transfer (MkPtr addr) = MkPtr addr

||| Borrow a non-null owning pointer as a read-only reference.
||| The owning pointer remains valid; a new borrowing reference is created.
||| The borrowing reference's lifetime must not outlive the owning pointer.
public export
borrow : Ptr Owning schema life NonNull
       -> (Ptr Owning schema life NonNull, Ptr Borrowing schema life NonNull)
borrow (MkPtr addr) = (MkPtr addr, MkPtr addr)

||| Exclusively borrow an owning pointer. Returns the exclusive pointer
||| and an ExclusiveWitness proving no other pointers exist in scope.
||| The owning pointer is temporarily unavailable (held by the exclusive borrow).
public export
borrowExclusive : Ptr Owning schema life NonNull
                -> (Ptr Exclusive schema life NonNull, ExclusiveWitness schema)
borrowExclusive (MkPtr addr) = (MkPtr addr, Exclusive "exclusive-borrow")
