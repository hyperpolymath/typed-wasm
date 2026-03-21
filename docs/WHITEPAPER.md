<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# typed-wasm: A 10-Level Type System for WebAssembly Linear Memory

**Jonathan D.A. Jewell**
*hyperpolymath*
`j.d.a.jewell@open.ac.uk`

**Version:** 0.1.0 | **Date:** 2026-03-21

---

## 1. Abstract

WebAssembly's linear memory is an untyped byte array shared across module
boundaries, and no existing type system covers the cross-language interface
where independently compiled modules read and write the same memory
regions. typed-wasm addresses this gap by applying TypeLL's 10-level type
safety framework — originally designed for database query languages — to
WebAssembly linear memory, treating contiguous memory segments as typed
region schemas and load/store operations as typed projections against those
schemas. The system is formalised in Idris2 using Quantitative Type Theory,
giving compile-time proofs of bounds safety, aliasing freedom, effect
purity, lifetime validity, and linearity — with zero runtime overhead
through proof erasure. The key contribution is **multi-module schema
agreement**: when Module A (compiled from Rust) shares linear memory with
Module B (compiled from ReScript), typed-wasm verifies at compile time that
both modules agree on the memory layout, field types, alignment, and
invariants — a property that neither source-level type system can express.

---

## 2. Problem Statement

### 2.1 The Untyped Byte Problem

WebAssembly's linear memory model exposes a flat byte array to all code
running within an instance. Instructions like `i32.load offset=16` and
`f64.store offset=24` operate on raw byte offsets with no schema, no field
names, and no type association between the offset and the data stored
there. The WASM specification validates that instructions are well-formed
and that accesses fall within the memory's allocated page range, but it
makes no claims about the *semantic* correctness of a memory access — it
cannot distinguish a valid read of a player's health points from a
type-confused reinterpretation of a floating-point velocity as an integer.

### 2.2 The Multi-Language Boundary

The problem becomes acute when multiple languages compile to WASM and share
linear memory. Consider:

- **Module A** (Rust): allocates a `Player` struct at offset 0 with layout
  `{ hp: i32 @ 0, speed: f64 @ 8, name: [u8; 32] @ 16 }`.
- **Module B** (ReScript/C): reads the same memory expecting
  `{ hp: i32 @ 0, velocity: f32 @ 4, label: [u8; 16] @ 8 }`.

Both modules compile independently. Both pass their own type checkers. But
Module B reads `speed` (an f64 at offset 8) as if it were `label` (a
16-byte string at offset 8), producing garbage. Worse, Module B writes
to offsets 4-7 believing it is setting a `velocity: f32` field that does
not exist in Module A's layout — silently corrupting the first four bytes
of Module A's `speed: f64`.

### 2.3 Concrete Bug Classes

The following bugs are undetectable by any source-level type system when
modules share linear memory:

1. **Type reinterpretation.** Module A stores `f64`; Module B loads `i64`
   from the same offset. The bit pattern is a valid i64, so no trap
   occurs, but the value is meaningless.

2. **Layout disagreement.** Module A pads fields to 8-byte alignment;
   Module B assumes packed layout. Every field after the first is read from
   the wrong offset.

3. **Null pointer divergence.** Module A uses 0 as null sentinel; Module B
   uses 0xFFFFFFFF. Each considers the other's "null" to be a valid
   pointer.

4. **Lifetime mismatch.** Module A frees a region; Module B continues
   holding a pointer to it. Module A reallocates the memory for a
   different purpose; Module B reads the new data as if it were the old
   structure.

5. **Double-free across modules.** Both modules believe they own the
   allocation and independently free it.

These are not theoretical. They are the everyday reality of WASM-based
plugin systems, game engines with scripting layers, and any architecture
where separately compiled modules share linear memory.

### 2.4 Why Existing Tools Fall Short

- **Rust's borrow checker** enforces ownership within Rust code. It has no
  jurisdiction over what a ReScript module does with shared memory.
- **WASM's validation** checks instruction encoding, not semantic
  correctness of memory access.
- **The WASM GC proposal** introduces managed reference types but does not
  cover linear memory.
- **Typed Assembly Language (TAL)** types individual instructions but lacks
  a schema system for structured memory regions and cross-module
  agreement.
- **Interface Types / Component Model** addresses function call boundaries
  but not shared mutable memory.

---

## 3. The Database-Memory Analogy

### 3.1 The Structural Correspondence

The insight behind typed-wasm is that WASM linear memory has the same
structure as a schemaless database, and the same class of type safety
framework applies to both.

| Database Concept | WASM Memory Concept | Structural Role |
|------------------|---------------------|-----------------|
| Table | Region (contiguous memory segment) | Named container of typed data |
| Row | Region instance (struct at offset) | Single record within the container |
| Column | Field (typed value at known offset) | Named, typed datum within a record |
| Schema | Region declaration | Compile-time description of layout |
| `SELECT col FROM table` | `region.get $handle .field` | Read projection through schema |
| `UPDATE table SET col = val` | `region.set $handle .field, val` | Write projection through schema |
| Foreign key | `ptr<@OtherRegion>` | Cross-region typed reference |
| CHECK constraint | Region invariant | Domain-specific validity rule |
| Index | Computed offset function | Efficient access path |
| Transaction | Effect-tracked scope | Controlled mutation boundary |

### 3.2 Why the Analogy Is Productive

This is not a loose metaphor. The correspondence is structural and
load-bearing:

**TypedQL's contribution** was to take an existing query language (SQL) and
layer 10 levels of type safety on top, so that every query is verified
against the schema at compile time. The framework works because SQL queries
are projections against a declared schema, and type safety means verifying
that the projection is compatible with the schema.

**typed-wasm's contribution** is to observe that WASM memory access
instructions are also projections — `i32.load offset=N` projects a 4-byte
integer from a flat byte store at position N — and that the same 10-level
framework applies if we give those projections a schema to project against.

The analogy yields concrete design decisions:

- **Region declarations** are table definitions. The grammar uses the same
  declarative style: `region Players { hp: i32; speed: f64; }` is
  analogous to `CREATE TABLE players (hp INTEGER, speed DOUBLE)`.

- **Import/export of region schemas** is analogous to shared database
  schemas across microservices. Module A exports its schema; Module B
  imports it and the type checker verifies agreement.

- **Cross-region invariants** (`invariant ValidTarget { across: Enemies,
  Players; holds: ... }`) are foreign key constraints — structural
  relationships between regions that must hold across all typed access
  paths.

- **`region.scan`** with a `where` clause is a SELECT with a WHERE clause.
  The analogy extends naturally to iteration, filtering, and aggregation
  over array regions.

### 3.3 Where the Analogy Diverges

Databases and WASM memory differ in important ways that the design must
respect:

- **Alignment and padding.** Database columns have no alignment concerns.
  Memory fields do. typed-wasm makes alignment explicit in region
  declarations and includes it in the type-checking contract.

- **Pointer arithmetic.** Databases do not have pointers. WASM linear
  memory is addressed by integer offsets. typed-wasm introduces pointer
  types (`ptr`, `ref`, `unique`) with ownership semantics that have no
  database counterpart.

- **Concurrency model.** Database transactions provide isolation. WASM
  shared memory provides none — concurrent writers can interleave at the
  byte level. typed-wasm's aliasing safety (Level 7) partially addresses
  this, but full concurrency safety requires session types, which are
  deferred to a future version.

---

## 4. The 10 Levels

TypeLL defines 10 levels of type safety for query-like operations against a
declared schema. typed-wasm adapts each level to the WASM memory domain.
Levels 1-6 have established analogues in existing type systems; Levels 7-10
extend beyond existing WASM proposals into ownership, effects, lifetimes,
and linearity at the memory level.

### Level 1: Instruction Validity

**Database:** Is the query syntactically valid?
**WASM:** Is the memory access expression well-formed?

Every typed-wasm access (`region.get`, `region.set`, `region.scan`,
`region.alloc`, `region.free`) must conform to the grammar. This is
parse-time safety — the first gate before any semantic analysis.

**WASM without typed-wasm:** WASM validates instruction encoding but has no
higher-level access syntax to validate.

### Level 2: Region-Binding Safety

**Database:** Do the referenced tables and columns exist?
**WASM:** Does the target region and field resolve to a declaration?

Every `region.get $target .field` must resolve `$target` to a declared
region and `.field` to a declared field within that region. Accessing
undeclared memory is a compile-time error, not a runtime corruption.

**Multi-module significance:** When Module B imports a region from Module A,
Level 2 ensures Module B's field accesses resolve against Module A's schema.

### Level 3: Type-Compatible Access

**Database:** Are the operand types compatible with the operation?
**WASM:** Does the load type match the field declaration?

If `Players.hp` is declared as `i32`, then `region.get $player .hp`
produces an `i32`. The WASM load instruction is generated from the field
type — the programmer never chooses the instruction variant.

**WASM without typed-wasm:** You can `f64.load` from an address written
with `i32.store`. WASM will reinterpret the bytes without complaint.

### Level 4: Null Safety

**Database:** Are nullable columns handled explicitly?
**WASM:** Are nullable pointers handled explicitly?

typed-wasm distinguishes `ptr<T>` (guaranteed non-null) from
`opt<ptr<T>>` (may be null). Accessing an optional value requires explicit
unwrapping through a null check. The type system statically tracks which
code paths have performed the check.

**WASM without typed-wasm:** All pointers are raw integers. The value 0 is
a valid memory address, indistinguishable from null.

### Level 5: Bounds-Proof Safety

**Database:** Is user input separated from query structure (injection-proof)?
**WASM:** Is the access provably within region bounds?

Regions have statically known sizes. Array regions have declared element
counts. The Idris2 prover verifies at compile time that field offsets fall
within the region size and array indices fall within the declared length.
Where static proof is impossible (e.g., dynamic indices from user input),
a minimal runtime bounds check is inserted — but only where necessary.

**WASM without typed-wasm:** WASM traps on access outside *linear memory*
but has no concept of bounds *within* linear memory.

### Level 6: Result-Type Safety

**Database:** Is the return type of the query known statically?
**WASM:** Is the return type of the memory access known statically?

The type of `region.get $player .hp` is `i32` because `hp: i32` in the
schema. This type propagates through bindings, function returns, and
subsequent operations. Type mismatches between producers and consumers are
caught at compile time.

### Level 7: Aliasing Safety

**Database:** How many writers exist for a given row?
**WASM:** Do mutable references to the same region avoid aliasing?

typed-wasm provides three pointer kinds:

| Kind | Aliasing | Guarantee |
|------|----------|-----------|
| `ref<T>` / `&` | Unlimited shared reads | No mutation through this reference |
| `unique<T>` / `&mut` | Exclusive | No other mutable reference exists |
| `ptr<T>` / `own` | Owning | Must free exactly once (Level 10) |

The Idris2 prover verifies that `&mut` references are exclusive at every
program point. This is the WASM-level equivalent of Rust's borrow checker,
but it operates on *region schemas*, not source-language values.

### Level 8: Effect-Tracking Safety

**Database:** Does this query read or write?
**WASM:** Are memory effects (Read/Write/Alloc/Free) declared and checked?

Every function declares its effects: `effects { ReadRegion(Players),
WriteRegion(Config) }`. A function declared `effects { Read }` cannot
write to any region. Effect subsumption allows a `Read`-only callback to
accept any function whose effects are a subset of `{ Read }`.

**WASM without typed-wasm:** A function exported as `get_player_hp` might
secretly write to memory, free a region, or allocate new memory. The caller
cannot know.

### Level 9: Lifetime Safety

**Database:** Is the data fresh enough (temporal validity)?
**WASM:** Is the reference still valid when used (spatial validity)?

Lifetime annotations scope reference validity. A reference to a region
cannot outlive the region's allocation. The prover verifies that no
`region.get` or `region.set` operates on freed memory, and that no
reference escapes the scope in which its target is live.

### Level 10: Linearity Safety

**Database:** Are connections and cursors used exactly once?
**WASM:** Is every owned resource consumed exactly once?

Linear types, implemented via Idris2's Quantitative Type Theory (QTT),
enforce that:

- Allocated memory is freed exactly once (no leaks, no double-free).
- Owning pointers are consumed exactly once (no duplication, no discard).

The QTT quantity `1` (linear) enforces exactly-once usage. The quantity `0`
(erased) allows compile-time-only proof witnesses. The quantity `w`
(unrestricted) allows normal unlimited use.

### Cross-Level Composition

The levels are not independent. Key compositions:

- **L5 + L7:** Bounds-proof plus aliasing safety proves that two `&mut`
  references never overlap in memory, even for different fields within the
  same region.
- **L8 + L9:** Effect-tracking plus lifetime safety proves that a
  read-only reference cannot observe a free effect on the same region.
- **L7 + L10:** Aliasing safety plus linearity gives the full ownership
  model — unique ownership, borrowing, and exactly-once destruction — at
  the WASM memory level.
- **L2 + L3 + multi-module:** Region-binding plus type-compatibility
  across module boundaries is the composition no existing tool provides.

---

## 5. The Multi-Module Breakthrough

### 5.1 The Problem in Detail

Consider a game engine where:

- **Module A** (Rust, compiled to WASM): manages game entities.
- **Module B** (ReScript, compiled to WASM via a JS/WASM bridge): provides
  the scripting/AI layer.
- Both share linear memory for performance — the scripting layer reads
  entity positions and health directly from shared memory rather than
  marshalling through function calls.

Module A defines its layout in Rust:

```rust
#[repr(C)]
struct Player {
    hp: i32,           // offset 0, size 4
    _padding: [u8; 4], // offset 4, size 4 (alignment)
    speed: f64,        // offset 8, size 8
    name: [u8; 32],    // offset 16, size 32
}
// Total: 48 bytes, aligned to 8
```

Module B, written in ReScript months later by a different developer,
assumes a packed layout:

```
// ReScript developer's mental model:
// hp:    i32 @ offset 0  (4 bytes)
// speed: f64 @ offset 4  (8 bytes) — WRONG: actual offset is 8
// name:  [u8; 32] @ offset 12       — WRONG: actual offset is 16
```

Module B reads `speed` from offset 4, which is padding bytes. It reads
`name` from offset 12, which overlaps the second half of `speed`. Neither
module's type checker can detect this because the mismatch exists at the
WASM level, below both source languages.

### 5.2 The typed-wasm Solution

In typed-wasm, Module A declares and exports its region schema:

```
region Player {
    hp: i32;
    speed: f64;
    name: u8[32];
    align 8;
}

export region Player;
```

Module B imports the schema:

```
import region Player from "module_a" {
    hp: i32;
    speed: f64;
    name: u8[32];
}
```

The typed-wasm checker performs **structural verification** at compile time:

1. **Field names match.** Both modules agree on `hp`, `speed`, `name`.
2. **Field types match.** Both declare `hp: i32`, `speed: f64`, etc.
3. **Layout compatibility.** The checker computes offsets from the field
   types and alignment. Module A's `align 8` produces `speed @ offset 8`,
   and the import must agree.
4. **Invariant agreement.** If Module A declares cross-region invariants,
   Module B's import must acknowledge them.

If Module B's import declared `speed: f32` instead of `speed: f64`, the
checker would reject it at compile time with an error identifying the
exact field, the expected type, and the declared type.

### 5.3 What This Enables

Multi-module schema agreement enables a new class of WASM application
architectures:

- **Plugin systems** where plugins access host memory safely. The host
  exports region schemas; plugins import them. Schema changes are caught
  at plugin compile time, not at runtime crash time.

- **Polyglot WASM compositions** where Rust, C, and ReScript modules share
  structured data through linear memory with compile-time guarantees that
  all modules agree on the layout.

- **Hot-reloadable modules** where a new version of a module can be
  checked for schema compatibility with existing modules before
  deployment.

---

## 6. GraalVM Implications

### 6.1 The Truffle Interop Problem

GraalVM's Truffle framework allows multiple languages (JavaScript, Python,
Ruby, R, LLVM-based languages) to interoperate by sharing objects through
the `InteropLibrary`. When a JavaScript object is passed to a Python
function, the Truffle runtime dispatches through `InteropLibrary` to
resolve member reads, writes, and invocations at runtime.

This works, but it has two costs:

1. **Runtime dispatch overhead.** Every cross-language member access goes
   through `InteropLibrary.readMember()`, which performs runtime type
   checks and conversions.
2. **No compile-time guarantees.** If a Ruby function expects a JavaScript
   object to have a `.length` property and the object does not, the error
   occurs at runtime. There is no compile-time verification that the
   producer and consumer agree on the shape of shared data.

### 6.2 typed-wasm as a Schema Layer for Truffle

typed-wasm's region schemas could serve as a compile-time contract between
Truffle languages:

- A JavaScript module exports `region SharedState { count: i32; label:
  u8[64]; }`.
- A Python module imports the same schema.
- The typed-wasm checker verifies agreement at compilation/AOT time.
- At runtime, the Truffle compiler can replace `InteropLibrary` dispatch
  with direct memory access at known offsets, because the schema agreement
  has been statically verified.

### 6.3 Concrete Benefits

**Eliminating runtime dispatch.** Where both modules agree on a region
schema, the Truffle partial evaluator can inline the memory access directly
— `InteropLibrary.readMember(obj, "count")` becomes `i32.load offset=0`.
The schema proof justifies the optimisation.

**Cross-language effect tracking.** If a JavaScript module declares
`effects { Read }` on a shared region, the Truffle compiler knows that
calls into this module will not mutate the region, enabling more aggressive
optimisation of the calling Python code.

**Detecting ABI breaks at compile time.** When a library author changes the
layout of a shared structure, all consuming modules are flagged by the
schema checker — before any code runs.

### 6.4 Scope of Applicability

This applies specifically to GraalVM's LLVM-based interop (Sulong) and
shared-memory interop paths. Truffle's object-based interop for managed
languages (JavaScript, Ruby) would require an adaptation layer that maps
object shapes to region schemas. This is feasible for Truffle's
`DynamicObject` system, which already tracks shapes internally, but is
not a trivial mapping and remains future work.

---

## 7. Formal Foundations

### 7.1 Idris2 and Dependent Types

typed-wasm's proofs are written in Idris2, a dependently typed language
where types can depend on values. This is essential for expressing
properties like "this array access is within bounds" as types:

- A region schema is a *value-level* description of memory layout: field
  names, types, sizes, offsets, alignment.
- A memory access is typed by the schema it projects through: the type of
  `region.get $player .hp` depends on the *value* of the `Player` schema
  declaration.
- Bounds proofs are dependent types that carry the evidence: `InBounds n
  (Array size)` is a type inhabited only when `n < size`.

### 7.2 Quantitative Type Theory

Idris2's QTT assigns a *quantity* to every variable binding:

| Quantity | Meaning | typed-wasm Use |
|----------|---------|----------------|
| `0` (erased) | Used only at compile time | Proof witnesses, schema metadata |
| `1` (linear) | Used exactly once at runtime | Owning pointers, allocation handles |
| `w` (unrestricted) | Used any number of times | Normal values, shared references |

This is the formal basis for Level 10 (linearity). An owning handle
`own region<Player>` is bound with quantity `1`, meaning the type checker
rejects any program that uses it zero times (leak) or more than once
(double-free/aliased mutation).

### 7.3 Proof Erasure and Zero Overhead

A critical property: all proofs are erased before code generation. The
Idris2 compiler's erasure analysis identifies all quantity-`0` terms —
which includes all proof witnesses, bounds evidence, and schema metadata
— and eliminates them from the generated code.

The result: **the runtime code is identical to hand-written WASM
load/store instructions.** The type safety is a compile-time property with
no runtime representation. There is no wrapper, no indirection, no tag
checking. A `region.get $player .hp` compiles to exactly `i32.load
offset=0` — the same instruction a C programmer would write. The
difference is that typed-wasm has proven this instruction is correct.

### 7.4 The Proof Language

typed-wasm's grammar includes proof-carrying statements:

```
proof bounds_safe {
    given: idx >= 0;
    given: idx < sizeof(Players);
    show:  InBounds(idx, Players);
    by:    bounds_check;
}
```

These are syntactic sugar for Idris2 proof terms. The `by` clause names a
proof tactic: `bounds_check`, `linearity`, `lifetime`, `alias_freedom`,
`effect_purity`, `induction`, or `rewrite`. The Idris2 totality checker
verifies that the proof is complete — no `believe_me`, no `assert_total`,
no escape hatches.

---

## 8. Implementation Architecture

### 8.1 Layer Overview

| Layer | Language | Role |
|-------|----------|------|
| ABI definitions | Idris2 | Dependent types defining region schemas, access typing rules, proof obligations |
| FFI bridge | Zig | C-ABI compatible runtime operations; cross-compilation to WASM targets |
| Surface parser | ReScript | Parse typed-wasm surface syntax to a typed AST |
| Proof engine | Idris2 totality checker | Verify Levels 5-10 properties at compile time |
| Code generator | Zig to WASM | Emit raw WASM load/store instructions from verified typed access |
| TypedQLiser plugin | Rust | Integration with the TypedQLiser ecosystem as a target language |

### 8.2 Idris2 ABI Layer

The ABI layer defines the core types:

- `RegionSchema`: a dependent record mapping field names to types, sizes,
  and offsets.
- `TypedAccess`: an access operation indexed by the region schema it
  projects through.
- `BoundsProof`: evidence that an offset is within a region's size.
- `LinearHandle`: a quantity-1 binding to an allocated region, ensuring
  exactly-once consumption.
- `EffectSig`: an effect set associated with a function, checked against
  the function body.

These definitions generate C headers via the standard Idris2-to-C
backend, which the Zig FFI layer consumes.

### 8.3 Zig FFI Layer

Zig provides the runtime bridge:

- Computes actual byte offsets from region schemas.
- Emits WASM load/store instructions.
- Handles WASM multi-memory (when multiple linear memories exist).
- Cross-compiles to `wasm32-freestanding` with zero runtime dependencies.

Zig was chosen for its native C ABI compatibility, built-in WASM target
support, and absence of runtime overhead.

### 8.4 ReScript Parser

The surface syntax parser is written in ReScript, consistent with the
VQL-UT parser. It parses the grammar defined in `spec/grammar.ebnf` and
produces a typed AST that is consumed by the Idris2 proof engine.

ReScript compiles to JavaScript/WASM via Deno, keeping the toolchain
within the hyperpolymath ecosystem.

### 8.5 TypedQLiser Integration

The TypedQLiser plugin makes typed-wasm a target within the broader
TypedQL ecosystem. TypedQLiser can:

- Generate typed-wasm region declarations from database schemas.
- Verify that a WASM module's memory layout matches a database table's
  schema — bridging the database-to-memory pipeline.
- Apply the same 10-level verification to both the query and the memory
  access that processes the query result.

---

## 9. Comparison with Related Work

### 9.1 Typed Assembly Language (TAL)

Morrisett et al.'s TAL (1999) introduced types for assembly instructions,
proving that well-typed assembly programs do not get stuck. TAL types
individual registers and stack slots.

**typed-wasm differs** by introducing region schemas — structured,
named, multi-field declarations with cross-module import/export. TAL types
individual memory cells; typed-wasm types structured memory regions. TAL
has no concept of cross-module schema agreement.

### 9.2 MSWasm (Memory-Safe WebAssembly)

MSWasm (Disselkoen et al., 2022) adds segments with bounds checking to
WASM, preventing spatial safety violations. Each memory segment carries a
base and bound, and all accesses are checked against these.

**typed-wasm differs** by adding schema-level types on top of bounds. A
segment in MSWasm knows its size but not its structure — you can access
any byte within bounds, regardless of what type was stored there.
typed-wasm adds the field-level type information that MSWasm lacks, plus
multi-module schema agreement, effect tracking, and linearity.

### 9.3 WASM GC Proposal

The WASM GC proposal introduces struct and array types that are managed by
the runtime garbage collector. These types are safe by construction — the
GC tracks liveness and prevents use-after-free.

**typed-wasm differs** by targeting linear memory, not GC-managed objects.
Linear memory is used by C, Rust, and other systems languages that manage
their own memory. The GC proposal does not help these languages. The two
systems are complementary: GC for managed languages, typed-wasm for
unmanaged linear memory.

### 9.4 Rust's Borrow Checker

Rust's ownership system (affine types with borrowing) prevents
use-after-free, double-free, and data races at the source level. It is the
most widely deployed ownership type system.

**typed-wasm differs** in scope: Rust's borrow checker operates within
Rust code. When Rust compiles to WASM and shares memory with a C or
ReScript module, the borrow checker has no jurisdiction over the other
module's accesses. typed-wasm operates at the WASM level, below all source
languages, and can verify the cross-language boundary.

typed-wasm's Levels 7, 9, and 10 are deliberately analogous to Rust's
ownership model — the contribution is applying this model at the WASM
memory layer rather than the source language layer.

### 9.5 Typed LLVM and Checked C

Typed LLVM (Lee et al.) adds types to LLVM IR. Checked C (Elliott et al.)
adds bounds-checked pointers to C. Both improve safety for single-language
compilation pipelines.

**typed-wasm differs** by operating at the WASM level, which is the
convergence point for multiple languages. Typed LLVM improves C/C++
compilation; typed-wasm improves the multi-language WASM composition.

### 9.6 WASM Component Model and Interface Types

The Component Model defines how WASM modules communicate through typed
function interfaces, with automatic marshalling of structured data across
module boundaries.

**typed-wasm differs** by addressing shared mutable memory, not function
call interfaces. The Component Model copies data across boundaries;
typed-wasm types *in-place* shared memory access. The two are
complementary: Component Model for isolation-based composition, typed-wasm
for shared-memory composition.

---

## 10. Limitations and Open Questions

### 10.1 Concurrency

typed-wasm v0.1 does not address concurrency. WASM shared memory with
atomics allows multiple threads to access the same linear memory
simultaneously. typed-wasm's aliasing safety (Level 7) prevents aliased
mutable references within a single thread, but does not prevent data races
across threads.

Extending typed-wasm with session types (as explored in
TypeQL-Experimental) could address this. A shared region accessed by
multiple threads would require a session protocol: acquire, read/write,
release. This is conceptually straightforward but formally complex, and is
deferred to a future version.

### 10.2 GC Interaction

When a WASM module uses both linear memory and GC-managed objects (which
is increasingly common as the GC proposal matures), the boundary between
the two is untyped. A GC reference stored in linear memory is just an
integer index; a linear memory pointer passed to GC code is opaque.

typed-wasm could be extended to type this boundary — e.g., a field type
`gcref<StructType>` that carries a proof that the index refers to a live
GC object. This requires cooperation with the WASM runtime, which is
beyond the scope of a static checker.

### 10.3 Dynamic Layout

Some WASM applications determine memory layout at runtime (e.g., JIT
compilers, interpreters with dynamic object models). typed-wasm's region
schemas are static declarations. Programs with fully dynamic layouts cannot
use typed-wasm without an adaptation layer that converts dynamic layout
information to static declarations at a coarser granularity.

### 10.4 Adoption Barrier

typed-wasm requires all participating modules to have typed-wasm
annotations. A Rust module compiled without typed-wasm region exports
cannot participate in cross-module schema verification. This creates a
chicken-and-egg problem: the benefits are strongest when all modules
participate, but each module bears the cost of annotation individually.

Mitigations include: automatic schema inference from Rust `#[repr(C)]`
structs, from C header files, and from WASM custom sections that compilers
already emit for debugging. These are implementation-level concerns, not
theoretical limitations.

### 10.5 Proof Completeness

Levels 5-10 rely on the Idris2 totality checker. If the programmer writes
a proof obligation that the checker cannot discharge, the programmer must
provide a manual proof or accept a runtime check. The system never silently
drops a proof obligation — an unproven obligation is a compile-time error,
not a silent downgrade.

However, the expressiveness of automatically dischargeable proofs is
bounded by the decidability of the underlying theories. Array bounds proofs
with non-linear arithmetic, for example, may require manual assistance.
The practical question is how often this occurs in real WASM modules — an
empirical question that requires deployment experience to answer.

### 10.6 WASM Specification Evolution

The WASM specification is evolving. Proposals for memory64, multi-memory,
stack switching, and exception handling may affect typed-wasm's assumptions.
The design is intentionally modular — region schemas are independent of
the WASM instruction set — but each new proposal requires evaluation for
compatibility.

---

## 11. Conclusion

WebAssembly's linear memory is the largest untyped shared mutable state
surface in modern software. Multiple languages compile to WASM; multiple
modules share linear memory; no existing type system covers the boundary
between them.

typed-wasm addresses this by recognising that WASM memory access has the
same structure as database queries: projections against a declared schema.
By applying TypeLL's 10-level type safety framework to memory regions,
typed-wasm provides:

1. **Region schemas** that declare memory layout with field names, types,
   sizes, alignment, and invariants.
2. **Multi-module schema agreement** that verifies at compile time that
   independently compiled modules agree on shared memory layout — the key
   contribution that no existing tool provides.
3. **10 levels of type safety** from basic instruction validity through
   bounds-proofs, aliasing safety, effect tracking, lifetime safety, and
   linearity — with formal proofs in Idris2 and zero runtime overhead
   through proof erasure.
4. **A practical architecture** with Idris2 for proofs, Zig for code
   generation, ReScript for parsing, and integration with the TypedQLiser
   ecosystem.

The implication extends beyond WASM. Any system where multiple languages
share untyped mutable state — GraalVM Truffle interop, JNI, FFI bridges,
shared memory IPC — faces the same class of bugs. typed-wasm demonstrates
that the database-query type safety framework is applicable to these
domains, and that dependent types with proof erasure can make the
verification zero-cost.

---

## References

- Morrisett, G., Walker, D., Crary, K., & Glew, N. (1999). From System F
  to Typed Assembly Language. *ACM Transactions on Programming Languages
  and Systems*.
- Disselkoen, C., Renner, J., Watt, C., Garber, T., Cauligi, S., &
  Stefan, D. (2022). MSWasm: Soundly Enforcing Memory-Safe Execution of
  Unsafe Code. *IEEE Symposium on Security and Privacy*.
- Brady, E. (2021). Idris 2: Quantitative Type Theory in Practice.
  *European Conference on Object-Oriented Programming (ECOOP)*.
- Atkinson, R., & Wadler, P. (2018). Quantitative Type Theory.
  *ACM/IEEE Symposium on Logic in Computer Science (LICS)*.
- Haas, A., Rossberg, A., Schuff, D.L., et al. (2017). Bringing the
  Web up to Speed with WebAssembly. *ACM SIGPLAN Conference on
  Programming Language Design and Implementation (PLDI)*.
- WebAssembly Community Group. (2024). GC Proposal.
  https://github.com/WebAssembly/gc
- WebAssembly Community Group. (2024). Component Model.
  https://github.com/WebAssembly/component-model
- GraalVM. (2024). Truffle Language Implementation Framework.
  https://www.graalvm.org/latest/graalvm-as-a-platform/language-implementation-framework/

---

*typed-wasm is part of the hyperpolymath TypeLL ecosystem.*
*Repository: https://github.com/hyperpolymath/typed-wasm*
