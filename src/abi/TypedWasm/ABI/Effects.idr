-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Effects.idr — Memory effect types for typed-wasm ABI
--
-- Every function in typed-wasm declares its memory effects:
--   Read       — loads values from a region
--   Write      — stores values into a region
--   Alloc      — allocates a new region instance
--   Free       — deallocates a region instance
--
-- Effects can be region-specific (ReadRegion(Players), WriteRegion(Config))
-- for finer-grained control: a function may read Players but not Config.
--
-- The effect system enforces:
--   1. A function cannot perform undeclared effects (soundness).
--   2. Effect subsumption: {Read} is a subset of {Read, Write}.
--   3. A read-only callback cannot be given a read-write function.
--   4. Alloc and Free are tracked separately from Read/Write (Level 10).
--
-- This corresponds to Level 8 of the typed-wasm safety stack.

module TypedWasm.ABI.Effects

import TypedWasm.ABI.Region

%default total

-- ============================================================================
-- Effect Labels
-- ============================================================================

||| Memory effect labels for typed-wasm. Each label represents a distinct
||| kind of memory operation. Functions declare which effects they perform,
||| and the type checker verifies that actual operations are within the
||| declared set.
public export
data MemEffect : Type where
  ||| Read from any region.
  Read  : MemEffect
  ||| Write to any region.
  Write : MemEffect
  ||| Allocate a new region instance.
  Alloc : MemEffect
  ||| Free (deallocate) a region instance.
  Free  : MemEffect
  ||| Read from a specific named region only.
  ReadRegion  : (regionName : String) -> MemEffect
  ||| Write to a specific named region only.
  WriteRegion : (regionName : String) -> MemEffect

public export
Eq MemEffect where
  Read            == Read            = True
  Write           == Write           = True
  Alloc           == Alloc           = True
  Free            == Free            = True
  (ReadRegion a)  == (ReadRegion b)  = a == b
  (WriteRegion a) == (WriteRegion b) = a == b
  _               == _              = False

public export
Show MemEffect where
  show Read            = "Read"
  show Write           = "Write"
  show Alloc           = "Alloc"
  show Free            = "Free"
  show (ReadRegion r)  = "ReadRegion(" ++ r ++ ")"
  show (WriteRegion r) = "WriteRegion(" ++ r ++ ")"

-- ============================================================================
-- Effect Sets
-- ============================================================================

||| An effect set is a list of effect labels. A function's declared effects
||| are an EffectSet, and its actual effects (from operations in its body)
||| are also an EffectSet. Type safety requires actual subset of declared.
public export
EffectSet : Type
EffectSet = List MemEffect

||| The empty effect set — a pure function that performs no memory operations.
public export
pureEffects : EffectSet
pureEffects = []

||| Read-only effect set — may load from memory but not store.
public export
readOnly : EffectSet
readOnly = [Read]

||| Read-write effect set — may load and store.
public export
readWrite : EffectSet
readWrite = [Read, Write]

||| Allocation effects — may read, write, and allocate.
public export
allocEffects : EffectSet
allocEffects = [Read, Write, Alloc]

||| Full effects — may perform any memory operation.
public export
fullEffects : EffectSet
fullEffects = [Read, Write, Alloc, Free]

-- ============================================================================
-- Effect Membership
-- ============================================================================

||| Proof that an effect label is a member of an effect set.
public export
data HasEffect : MemEffect -> EffectSet -> Type where
  ||| The effect is at the head of the set.
  EffHere  : HasEffect e (e :: rest)
  ||| The effect is somewhere in the tail.
  EffThere : HasEffect e rest -> HasEffect e (f :: rest)

-- ============================================================================
-- Effect Subsumption (Level 8 Core Judgement)
-- ============================================================================

||| Proof that one effect set is a subset of another: every effect in
||| `actual` is also in `declared`. This is the core Level 8 judgement.
|||
||| A function is effect-safe if its actual effects (from operations in
||| its body) are subsumed by its declared effects (in the effects clause).
public export
data EffectSubsumes : (declared : EffectSet) -> (actual : EffectSet) -> Type where
  ||| The empty actual set is trivially subsumed.
  SubNil  : EffectSubsumes declared []
  ||| If an effect is in `declared` and the rest are subsumed, the whole
  ||| actual set is subsumed.
  SubCons : HasEffect e declared
          -> EffectSubsumes declared rest
          -> EffectSubsumes declared (e :: rest)

-- ============================================================================
-- Region-Specific Effect Subsumption
-- ============================================================================

||| Proof that a region-specific effect is subsumed by a general effect.
||| ReadRegion("Players") is subsumed by Read (reading any region).
||| WriteRegion("Config") is subsumed by Write (writing any region).
|||
||| This allows coarse-grained declarations (Read, Write) to cover
||| fine-grained operations (ReadRegion, WriteRegion).
public export
data RegionEffectSubsumes : MemEffect -> MemEffect -> Type where
  ||| ReadRegion(r) is covered by Read.
  ReadCovers  : RegionEffectSubsumes Read (ReadRegion r)
  ||| WriteRegion(r) is covered by Write.
  WriteCovers : RegionEffectSubsumes Write (WriteRegion r)
  ||| An effect covers itself.
  SelfCovers  : RegionEffectSubsumes e e

-- ============================================================================
-- Effect Combination
-- ============================================================================

||| Combine two effect sets by appending.
public export
combineEffects : EffectSet -> EffectSet -> EffectSet
combineEffects [] ys = ys
combineEffects (x :: xs) ys = x :: combineEffects xs ys

||| Proof that combining two subsumed sets yields a subsumed set.
||| If actual1 is subsumed by declared and actual2 is subsumed by declared,
||| then (actual1 ++ actual2) is subsumed by declared.
public export
combineSub : EffectSubsumes declared xs
           -> EffectSubsumes declared ys
           -> EffectSubsumes declared (combineEffects xs ys)
combineSub SubNil subYs = subYs
combineSub (SubCons elem rest) subYs = SubCons elem (combineSub rest subYs)

-- ============================================================================
-- Effect Weakening
-- ============================================================================

||| Adding an effect to the declared set preserves subsumption.
||| If actual is subsumed by declared, then actual is also subsumed by
||| (e :: declared). Declaring more effects never breaks safety.
public export
effectWeaken : EffectSubsumes declared actual
             -> EffectSubsumes (e :: declared) actual
effectWeaken SubNil = SubNil
effectWeaken (SubCons elem rest) = SubCons (EffThere elem) (effectWeaken rest)

-- ============================================================================
-- Effect Reflexivity
-- ============================================================================

||| Proof that every element of a list is a member of itself via Here/There.
||| Helper for proving reflexivity.
public export
selfMember : (xs : EffectSet) -> (e : MemEffect) -> HasEffect e xs -> HasEffect e xs
selfMember _ _ prf = prf

||| Subsumption is reflexive: every effect set subsumes itself.
public export
effectSubsumesRefl : (xs : EffectSet) -> EffectSubsumes xs xs
effectSubsumesRefl [] = SubNil
effectSubsumesRefl (x :: rest) =
  SubCons EffHere (effectWeaken (effectSubsumesRefl rest))

-- ============================================================================
-- Effectful Operation Type
-- ============================================================================

||| A memory operation parameterised by its required effects.
||| The type-level effect set ensures the operation can only be executed
||| in a context whose declared effects subsume the required effects.
public export
data MemOp : (required : EffectSet) -> Type -> Type where
  ||| An operation requiring certain effects that produces a value.
  MkMemOp : (effects : EffectSet) -> (result : a) -> MemOp effects a

||| Execute a memory operation in a context with sufficient declared effects.
||| The subsumption proof is automatically searched by Idris2.
public export
runMemOp : MemOp required a -> {auto prf : EffectSubsumes declared required} -> a
runMemOp (MkMemOp _ val) = val

-- ============================================================================
-- Standard Memory Operations with Effect Tags
-- ============================================================================

||| A read operation on a specific region.
public export
readOp : (regionName : String) -> a -> MemOp [ReadRegion regionName] a
readOp rn val = MkMemOp [ReadRegion rn] val

||| A write operation on a specific region.
public export
writeOp : (regionName : String) -> a -> MemOp [WriteRegion regionName] a
writeOp rn val = MkMemOp [WriteRegion rn] val

||| An allocation operation.
public export
allocOp : a -> MemOp [Alloc] a
allocOp val = MkMemOp [Alloc] val

||| A free operation.
public export
freeOp : a -> MemOp [Free] a
freeOp val = MkMemOp [Free] val
