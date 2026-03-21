<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# typed-wasm: Applying Database Query Type Safety to WebAssembly Linear Memory

**Jonathan D.A. Jewell**
The Open University, Milton Keynes, UK
`j.d.a.jewell@open.ac.uk`

**Draft — March 2026**

---

**Keywords:** WebAssembly, type safety, dependent types, linear memory,
multi-module verification, quantitative type theory, memory safety

**Categories:** D.3.1 [Programming Languages]: Formal Definitions and Theory;
D.2.4 [Software Engineering]: Software/Program Verification;
F.3.1 [Logics and Meanings of Programs]: Specifying and Verifying Programs

---

## Abstract

WebAssembly (Wasm) linear memory is an untyped byte array shared across
module boundaries. When independently compiled modules — potentially from
different source languages — read and write the same memory regions, no
existing type system covers the cross-module interface. We present
**typed-wasm**, a type system that applies a 10-level type safety
framework, originally developed for database query languages, to Wasm
linear memory. The system treats contiguous memory segments as *typed
region schemas* and load/store operations as *typed projections* verified
against those schemas at compile time. We formalise the system in Idris 2
using Quantitative Type Theory (QTT), providing proofs of bounds safety,
aliasing freedom, effect purity, lifetime validity, and linearity — all
erased before code generation, yielding zero runtime overhead. Our
principal contribution is **multi-module schema agreement**: a static
verification that independently compiled Wasm modules agree on the
layout, types, alignment, and invariants of shared memory regions — a
property that no source-level type system, and no existing Wasm proposal,
can express.

---

## 1. Introduction

The WebAssembly specification [Haas et al. 2017] defines a stack-based
virtual machine with strong instruction-level type safety: the validator
rejects programs whose stack operations are type-incorrect, and the
structured control flow ensures that branches target valid labels. These
properties make Wasm a safe compilation target for individual languages.

However, Wasm's linear memory — the flat byte array that serves as the
heap for compiled C, Rust, and other systems languages — is entirely
untyped. An `i32.load offset=0` and an `f64.load offset=0` targeting the
same address are both valid instructions, regardless of what was actually
stored there. The Wasm validator checks that the instruction encoding is
correct, not that the memory access is semantically meaningful.

This gap becomes a safety hazard when multiple independently compiled
modules share linear memory — an increasingly common pattern in plugin
architectures, game engines, and polyglot Wasm compositions. If Module A
(compiled from Rust) writes a struct to shared memory and Module B
(compiled from C or ReScript) reads the same memory with a different
layout assumption, the result is silent data corruption undetectable by
either source-level type system.

We observe that this problem has the same structure as untyped database
access: programs issue "queries" (load/store instructions) against a
"schema" (memory layout) with no static guarantee that the query is
compatible with the schema. The database query language community has
developed mature solutions to this problem, culminating in progressive
type safety frameworks that verify queries against schemas at compile time.

This paper presents typed-wasm, which applies this approach to Wasm
linear memory. Our contributions are:

1. **The database-memory analogy as a design principle** (Section 3):
   a structural correspondence between database schemas and memory
   region declarations, between queries and typed memory access, that
   yields a concrete grammar and type system.

2. **A 10-level progressive type safety framework for Wasm memory**
   (Section 4): adapting established levels (parse-time validity,
   schema binding, type compatibility, null safety, bounds proofs,
   result typing) and research levels (aliasing safety, effect
   tracking, lifetime safety, linearity) from the database domain
   to the memory domain.

3. **Multi-module schema agreement** (Section 5): a static verification
   that independently compiled Wasm modules agree on shared memory
   layout — the principal contribution, addressing a class of bugs
   that no existing tool can detect.

4. **A formalisation in Idris 2 with QTT** (Section 7): dependent types
   that prove safety properties at compile time, with proof erasure
   yielding identical runtime code to hand-written Wasm.

---

## 2. Problem Statement

### 2.1 The Untyped Byte Array

Wasm's linear memory model [WebAssembly Specification 2024, §5.3]
exposes a resizable byte array to all code within an instance. Memory
access instructions (`i32.load`, `f64.store`, etc.) take an integer
offset and an alignment hint. The Wasm validator ensures that the
alignment is valid for the instruction and that the access falls within
the allocated page range, but it imposes no constraints on the
*semantic content* at the accessed offset.

Formally, if $M$ is the linear memory (a function from byte offsets to
bytes), then `i32.load offset=k` computes $M[k] | (M[k+1] \ll 8) |
(M[k+2] \ll 16) | (M[k+3] \ll 24)$ regardless of what was stored at
offsets $k$ through $k+3$. The instruction cannot fail for type reasons
— only for out-of-bounds access beyond the memory's page limit.

### 2.2 The Cross-Module Boundary Problem

When multiple modules share linear memory, each module compiles with its
own struct layout assumptions. Consider:

- **Module A** (Rust, `#[repr(C)]`): `Player { hp: i32 @ 0, _pad: [u8;4] @ 4, speed: f64 @ 8, name: [u8;32] @ 16 }` — 48 bytes, 8-byte aligned.
- **Module B** (C, packed): `player_t { int hp @ 0, double speed @ 4, char name[32] @ 12 }` — 44 bytes, unaligned.

Module B reads `speed` from offset 4, which in Module A's layout is
padding. Module B writes `name` starting at offset 12, which overlaps
Module A's `speed` field. Neither module's type checker detects this:
Rust's borrow checker validates within Rust; C's type system validates
within C. The mismatch exists at the Wasm level, below both.

### 2.3 Bug Taxonomy

We identify five classes of cross-module memory bugs:

| Class | Description | Consequence |
|-------|-------------|-------------|
| **B1. Type reinterpretation** | Load type differs from store type at same offset | Silent value corruption |
| **B2. Layout disagreement** | Modules assume different field offsets | All fields after the first are misread |
| **B3. Null sentinel divergence** | Modules disagree on the null representation | Valid pointers treated as null, or vice versa |
| **B4. Lifetime mismatch** | One module frees memory another still references | Use-after-free, data from reallocated memory |
| **B5. Ownership confusion** | Multiple modules believe they own the allocation | Double-free, heap corruption |

These bugs share a common root: the absence of a shared schema that all
modules agree upon and that a static checker can verify.

### 2.4 Insufficiency of Existing Approaches

| Approach | What it covers | What it misses |
|----------|---------------|----------------|
| Rust borrow checker | Ownership within Rust | Cross-module access from non-Rust code |
| Wasm validation | Instruction encoding, page bounds | Semantic correctness within pages |
| Wasm GC proposal | Managed reference types | Linear memory (unmanaged) |
| Typed Assembly Language [Morrisett et al. 1999] | Register/stack types | Structured regions, cross-module schemas |
| MSWasm [Disselkoen et al. 2022] | Segment bounds checking | Field-level types, schema agreement |
| Component Model [WebAssembly CG 2024] | Function call interfaces | Shared mutable memory |

---

## 3. The Database-Memory Analogy

### 3.1 Structural Correspondence

The TypedQL framework [Jewell 2026] provides 10 progressive levels of
type safety for database query languages. Its central mechanism is
verifying *query projections* against a *declared schema* at compile
time. We observe that Wasm memory access has identical structure:

| Database | Wasm Memory | Structural Role |
|----------|-------------|-----------------|
| Table | Region | Named container of typed records |
| Row | Region instance | Single record at a computed offset |
| Column | Field | Named, typed datum within a record |
| Schema | Region declaration | Compile-time layout specification |
| `SELECT col FROM table` | `region.get $r .field` | Read projection |
| `UPDATE table SET col = v` | `region.set $r .field, v` | Write projection |
| Foreign key | `ptr<@OtherRegion>` | Cross-region typed reference |
| `CHECK` constraint | `invariant { ... }` | Domain validity rule |

### 3.2 Why the Analogy Is Load-Bearing

This is not a surface-level metaphor. The correspondence determines
concrete design decisions:

1. **Region declarations** use declarative syntax isomorphic to `CREATE TABLE`:
   `region Players[100] { hp: i32; speed: f64; align 8; }`.

2. **Import/export of region schemas** mirrors shared database schemas
   across services. Module A exports; Module B imports; the checker
   verifies structural compatibility.

3. **Cross-region invariants** are foreign key constraints over memory:
   `invariant { across: Enemies, Players; holds: forall e. 0 <= e.target_id < 4096; }`.

4. **`region.scan` with `where`** is `SELECT * FROM region WHERE predicate`,
   extending naturally to iteration, filtering, and aggregation over
   array regions.

The 10-level framework transfers directly because the safety properties
are properties of *projections against schemas*, independent of whether
the schema describes a database table or a memory region.

### 3.3 Where the Analogy Diverges

Three aspects of Wasm memory have no direct database counterpart:

- **Alignment and padding.** Memory fields require alignment to
  natural boundaries. typed-wasm makes alignment explicit in
  declarations and includes it in the type-checking contract.

- **Pointer arithmetic.** Wasm linear memory is addressed by integer
  offsets. typed-wasm introduces pointer types (`ptr`, `ref`, `unique`)
  with ownership semantics borrowed from substructural type theory.

- **Concurrency.** Database transactions provide isolation; Wasm shared
  memory provides none. typed-wasm's aliasing safety (Level 7) addresses
  single-threaded aliasing; concurrent access is deferred to future work.

---

## 4. The 10 Levels of Type Safety for Wasm Memory

TypeLL defines a progressive stack of 10 type safety levels. Each level
addresses a specific class of failure. Levels are cumulative: a program
cannot achieve Level $n$ without satisfying Levels 1 through $n-1$.
Simple operations exit early — a read from a singleton region achieves
Level 6 with no ownership, effect, lifetime, or linearity analysis.

### 4.1 Established Levels (1–6)

**Level 1 — Instruction Validity.** The access expression conforms to the
typed-wasm grammar. Analogous to parse-time safety for queries. Wasm
itself validates instruction encoding but not higher-level access structure.

**Level 2 — Region-Binding.** Every `region.get $target .field` resolves
`$target` to a declared region and `.field` to a declared field. Analogous
to schema binding. Wasm has no concept of named regions or fields.

**Level 3 — Type-Compatible Access.** The result type of a memory access
is determined by the field declaration, not by the programmer's choice of
load instruction. If `hp: i32`, then `region.get $p .hp` produces `i32`
and compiles to `i32.load` — never `f64.load`. Analogous to
type-compatible operations in queries.

**Level 4 — Null Safety.** The type system distinguishes `ptr<T>`
(non-nullable) from `opt<ptr<T>>` (nullable). Accessing a nullable
value requires explicit unwrapping. Analogous to null safety in query
result handling.

**Level 5 — Bounds-Proof.** Every memory access is provably within the
region's bounds. For static indices, the Idris 2 prover verifies the
bound at compile time. For dynamic indices, a minimal runtime check is
inserted only where the prover cannot discharge the obligation. Analogous
to injection-proof safety (separation of structure from data).

**Level 6 — Result-Type.** The return type of every memory access
expression is statically known and propagated through bindings and
function returns. Analogous to result-type safety in queries.

### 4.2 Research Levels (7–10)

**Level 7 — Aliasing Safety.** Mutable references (`&mut`) to the same
region do not alias. typed-wasm provides three pointer kinds:

- `&` (shared borrow): unlimited concurrent readers, no mutation.
- `&mut` (exclusive borrow): exactly one mutable reference, no concurrent readers.
- `own` (owning): single owner, must transfer or free (Level 10).

The prover verifies exclusivity at every program point. This is
structurally analogous to Rust's borrow discipline, but operates at the
Wasm region schema level rather than the source language level.

**Level 8 — Effect Tracking.** Functions declare their memory effects:
`effects { ReadRegion(Players), WriteRegion(Config) }`. A function
declared read-only cannot perform writes. Effects are checked by
subsumption: $\mathit{actual} \subseteq \mathit{declared}$. Analogous to
distinguishing `SELECT` from `UPDATE` in queries.

**Level 9 — Lifetime Safety.** References carry lifetime annotations
scoping their validity. A reference with lifetime $\ell$ is valid only
while $\ell$ is live. The prover verifies that no reference is used after
the memory it points to has been freed. Analogous to temporal freshness
in queries.

**Level 10 — Linearity.** Owning handles are bound with QTT quantity 1,
enforcing exactly-once consumption. An allocation must be freed exactly
once: the type checker rejects programs with zero uses (leak) or two uses
(double-free) of the handle. This composes with Level 9: freeing
invalidates the lifetime, making all references with that lifetime
unusable. Analogous to connection linearity in database access.

### 4.3 Cross-Level Composition

The levels compose to provide compound guarantees:

- **L5 ∧ L7:** Bounds-proof plus aliasing safety proves that two exclusive
  references never overlap in memory, even for different fields within the
  same region.
- **L8 ∧ L9:** Effect tracking plus lifetime safety proves that a
  read-only reference cannot observe a free effect on its target region.
- **L7 ∧ L10:** Aliasing safety plus linearity yields the full ownership
  model at the Wasm memory level.
- **L2 ∧ L3 ∧ multi-module:** Region-binding plus type-compatibility
  across module boundaries is the composition unique to typed-wasm.

---

## 5. Multi-Module Schema Agreement

### 5.1 The Verification Problem

Given Module A exporting region $R_A$ with schema $S_A$ and Module B
importing region $R_B$ (claiming to correspond to $R_A$) with schema
$S_B$, verify that $S_B$ is structurally compatible with $S_A$.

### 5.2 Compatibility Relation

We define structural compatibility $S_B \preceq S_A$ (import compatible
with export) as follows:

**Definition 1 (Field Compatibility).** Fields $f_A$ and $f_B$ are
compatible, written $f_B \sim f_A$, iff:
- $f_B.\mathit{name} = f_A.\mathit{name}$
- $f_B.\mathit{type} = f_A.\mathit{type}$ (strict equality, no implicit conversions)
- $f_B.\mathit{offset} = f_A.\mathit{offset}$ (computed from types and alignment)

**Definition 2 (Schema Compatibility).** $S_B \preceq S_A$ iff:
- For every field $f_B \in S_B$, there exists $f_A \in S_A$ such that $f_B \sim f_A$.
- $S_B.\mathit{alignment} = S_A.\mathit{alignment}$
- $S_B.\mathit{instance\_count} = S_A.\mathit{instance\_count}$

Note that $\preceq$ permits $S_B$ to be a *subset* of $S_A$: Module B
may import fewer fields than Module A exports. Module B simply cannot
access the omitted fields. This is analogous to a database view that
projects a subset of columns.

**Definition 3 (Multi-Module Agreement).** A set of modules
$\{M_1, \ldots, M_n\}$ sharing region $R$ satisfies multi-module
agreement iff exactly one module $M_e$ exports $R$ with schema $S_e$,
and for every importing module $M_i$ with schema $S_i$, $S_i \preceq S_e$.

### 5.3 Formalisation

In the Idris 2 ABI layer, schema agreement is a dependent type:

```idris
data CompatCertificate : Type where
  MkCompat : (agreement : SchemaAgreement)
          -> (alignment : AlignmentAgrees ea ia)
          -> (instances : InstanceCountAgrees ec ic)
          -> CompatCertificate
```

Constructing a `CompatCertificate` requires providing proofs of each
component. If any proof cannot be constructed — a field name mismatch,
a type difference, an alignment disagreement — the certificate cannot
be produced, and the program is rejected at compile time.

### 5.4 Diagnostic Reporting

When verification fails, the checker produces structured diagnostics:

```
Schema mismatch for region 'Player' imported by module_b from module_a:
  Field 'speed': type mismatch
    Expected (from module_a): f64
    Found (in module_b):      f32
  Field 'name': offset mismatch
    Expected (from module_a): offset 16 (8-byte aligned)
    Found (in module_b):      offset 12 (assumes packed layout)
```

### 5.5 Practical Applications

Multi-module schema agreement enables:

- **Plugin architectures** where the host exports region schemas and
  plugins import them. Schema-breaking changes are caught at plugin
  compile time.

- **Polyglot Wasm compositions** where Rust, C, and ReScript modules
  share structured data with compile-time layout verification.

- **Hot-reloadable modules** where a new module version is checked for
  schema compatibility with existing modules before deployment.

---

## 6. Implications for GraalVM

GraalVM's Truffle framework [Würthinger et al. 2017] enables
cross-language interoperation through `InteropLibrary`, which dispatches
member reads, writes, and invocations at runtime. When a JavaScript
object is accessed from Python code, `InteropLibrary.readMember()` performs
runtime type checking and conversion.

This has two costs: runtime dispatch overhead and the absence of
compile-time guarantees. typed-wasm's region schemas could serve as a
compile-time contract between Truffle languages:

1. Language A exports a region schema describing shared state.
2. Language B imports the schema.
3. The checker verifies agreement at AOT compilation time.
4. The Truffle partial evaluator replaces `InteropLibrary` dispatch with
   direct memory access at known offsets, justified by the schema proof.

This applies specifically to GraalVM's native interop paths (Sulong,
shared memory). Adapting the approach to Truffle's object-based interop
for managed languages requires mapping object shapes to region schemas,
which is feasible given Truffle's `DynamicObject` shape tracking but
remains future work.

---

## 7. Formal Foundations

### 7.1 Idris 2 and Dependent Types

typed-wasm's proofs are written in Idris 2 [Brady 2021], a dependently
typed language where types may depend on values. This is necessary
because memory safety properties inherently depend on values: "index $i$
is within the bounds of array of size $n$" is a proposition over the
value of $i$.

A region schema is a value-level record:

```idris
data Schema : List (String, FieldType) -> Type where
  Nil  : Schema []
  (::) : Field name ty -> Schema rest -> Schema ((name, ty) :: rest)
```

A typed access is indexed by the schema:

```idris
data TypedGet : Schema fields -> (name : String) -> FieldType -> Type where
  GetHere  : TypedGet (MkField {name} {ty} :: rest) name ty
  GetThere : TypedGet rest name ty -> TypedGet (f :: rest) name ty
```

The result type of `region.get $r .name` is *computed* from the schema,
not declared by the programmer.

### 7.2 Quantitative Type Theory

Idris 2's QTT [Atkey 2018; McBride 2016] assigns quantities to bindings:

| Quantity | Usage | typed-wasm application |
|----------|-------|------------------------|
| 0 (erased) | Compile-time only | Proof witnesses, schema metadata, bounds evidence |
| 1 (linear) | Exactly once at runtime | Owning handles, allocation tokens |
| $\omega$ (unrestricted) | Any number of times | Normal values, shared references |

Level 10 is implemented by binding allocation handles with quantity 1:

```idris
freeRegion : (1 _ : LinHandle token) -> RegionLive token -> FreeResult
```

The `(1 _)` annotation means the type checker rejects any program where
the handle is used zero times (leak) or more than once (double-free).

### 7.3 Proof Erasure

All quantity-0 terms — which includes all proof witnesses, bounds
evidence, schema metadata, compatibility certificates, and lifetime
annotations — are erased by the Idris 2 compiler before code generation.

**Theorem (informal).** The runtime representation of a well-typed
typed-wasm program is identical to the Wasm instructions that a
hand-written program would produce. The type safety is a compile-time
property with no runtime manifestation.

This is the zero-overhead guarantee: `region.get $player .hp` compiles
to exactly `i32.load offset=0`, with the proof that this instruction
is correct existing only during compilation.

### 7.4 Soundness Sketch

We conjecture the following soundness property:

**Conjecture 1 (typed-wasm soundness).** If a typed-wasm program
type-checks at all 10 levels, then the compiled Wasm program:
- (a) never performs a type-confused memory read (L3),
- (b) never accesses memory outside a declared region (L5),
- (c) never holds aliased mutable references (L7),
- (d) never performs an undeclared memory effect (L8),
- (e) never dereferences a freed region (L9), and
- (f) never leaks or double-frees an allocation (L10).

A full mechanised proof is future work. The current Idris 2 formalisation
provides dependent-type-level evidence for properties (a)–(f), verified
by the totality checker, but does not yet connect to a formal Wasm
operational semantics.

---

## 8. Implementation Architecture

| Layer | Language | Role |
|-------|----------|------|
| ABI definitions | Idris 2 | Dependent types: region schemas, access rules, proof obligations |
| FFI bridge | Zig | C-ABI runtime: region management, typed load/store, WASM codegen |
| Surface parser | ReScript | Parse `.twasm` syntax to typed AST |
| Proof engine | Idris 2 totality checker | Discharge levels 5–10 obligations |
| Code generator | Zig → Wasm | Emit raw Wasm instructions from verified typed access |
| Ecosystem plugin | Rust (TypedQLiser) | Integration as a TypedQLiser target language |

**Zig FFI.** Zig provides native C ABI compatibility, built-in
`wasm32-freestanding` target support, cross-compilation without runtime
dependencies, and memory-safe defaults. Region handles encode base
offset, schema ID, generation counter (for lifetime tracking), and
ownership flag in a 64-bit value.

**ReScript parser.** The surface syntax parser is written in ReScript,
consistent with the VQL-UT parser in the TypedQL ecosystem. ReScript
compiles to JavaScript/Wasm via Deno.

**TypedQLiser integration.** typed-wasm implements the `QueryLanguagePlugin`
trait from TypedQLiser, making Wasm memory a target alongside SQL,
GraphQL, and VQL. This enables end-to-end verification: a database query
is type-checked by TypedQLiser, and the memory region holding its results
is type-checked by typed-wasm.

---

## 9. Related Work

**Typed Assembly Language.** Morrisett et al. [1999] introduced TAL,
assigning types to registers and stack slots to prove progress and
preservation for assembly programs. typed-wasm extends this approach
with structured region schemas, cross-module import/export, and a
10-level progressive framework. TAL types individual memory cells;
typed-wasm types structured multi-field regions.

**MSWasm.** Disselkoen et al. [2022] add memory segments with bounds
checking to Wasm, enforcing spatial safety. typed-wasm builds on this
by adding field-level types within bounded regions, cross-module schema
agreement, effect tracking, and linearity. The two are complementary:
MSWasm ensures access is within bounds; typed-wasm ensures access is
also type-correct within those bounds.

**Wasm GC Proposal.** The GC proposal [WebAssembly CG 2024a] introduces
managed struct and array types. These are type-safe by construction but
apply only to GC-managed objects, not to linear memory. Systems languages
(C, Rust) that manage their own memory cannot benefit. typed-wasm and
Wasm GC are complementary.

**Wasm Component Model.** The Component Model [WebAssembly CG 2024b]
types function call interfaces with automatic marshalling. It addresses
isolation-based composition (copying data across boundaries). typed-wasm
addresses shared-memory composition (typing in-place access). Both are
valid architectural choices; typed-wasm covers the case where copying is
too expensive.

**Rust Ownership.** Rust's affine type system [Jung et al. 2018]
prevents use-after-free, double-free, and data races within Rust code.
typed-wasm's Levels 7, 9, and 10 are deliberately analogous but operate
at the Wasm level, covering cross-language boundaries that Rust cannot reach.

**Checked C and Typed LLVM.** Checked C [Elliott et al. 2018] adds
bounds-checked pointers to C. Typed LLVM [Lee et al.] adds types to LLVM
IR. Both improve single-language compilation pipelines. typed-wasm
operates at the Wasm convergence point, where multiple source languages meet.

**Substructural Type Systems.** Linear types [Wadler 1990], uniqueness
types [Barendsen and Smetsers 1996], and quantitative type theory
[Atkey 2018] provide the theoretical foundation for typed-wasm's Levels
7–10. Our contribution is not new type theory but rather the application
of these ideas to the specific problem of cross-module Wasm memory safety.

---

## 10. Limitations and Future Work

**Concurrency.** typed-wasm v0.1 does not address Wasm shared memory
with atomics. Concurrent access to shared regions requires session types
or fractional permissions, which are explored in the TypeQL-Experimental
project but not yet integrated.

**GC interaction.** The boundary between linear memory and GC-managed
objects is currently untyped. A `gcref<T>` field type is conceivable but
requires runtime cooperation beyond static checking.

**Dynamic layouts.** Programs that determine memory layout at runtime
(JIT compilers, dynamic object models) cannot use static region
declarations without an adaptation layer.

**Adoption barrier.** All participating modules must carry typed-wasm
annotations. Automatic schema inference from `#[repr(C)]` attributes,
C headers, and Wasm debug custom sections could lower this barrier.

**Proof completeness.** Levels 5–10 depend on the Idris 2 totality
checker. Complex arithmetic bounds may require manual proof assistance.
The practical frequency of this in real Wasm modules is an empirical
question.

**Mechanised soundness.** The soundness conjecture (Section 7.4) is
not yet mechanically verified against a formal Wasm operational
semantics. Connecting the Idris 2 formalisation to an existing Wasm
mechanisation (e.g., WasmCert [Watt 2018]) is a priority.

---

## 11. Conclusion

Wasm's linear memory is the largest untyped shared mutable state surface
in modern software. Multiple languages compile to Wasm; multiple modules
share linear memory; no existing type system covers the boundary between
them.

typed-wasm addresses this by recognising that Wasm memory access has the
same structure as database queries — projections against a declared
schema. By applying a 10-level type safety framework to memory regions,
typed-wasm provides:

1. **Region schemas** that declare memory layout with field names, types,
   alignment, and invariants.
2. **Multi-module schema agreement** that statically verifies layout
   compatibility across independently compiled modules.
3. **10 levels of progressive type safety** from instruction validity
   through linearity, with formal proofs in Idris 2 and zero runtime
   overhead through proof erasure.
4. **A practical architecture** integrating Idris 2, Zig, ReScript, and
   the TypedQLiser ecosystem.

The implication extends beyond Wasm. Any system where multiple languages
share untyped mutable state — GraalVM Truffle interop, JNI, FFI bridges,
shared memory IPC — faces the same class of bugs. typed-wasm
demonstrates that database query type safety is a transferable framework
for these domains.

---

## References

Atkey, R. (2018). Syntax and Semantics of Quantitative Type Theory.
*ACM/IEEE Symposium on Logic in Computer Science (LICS)*.

Barendsen, E. and Smetsers, S. (1996). Uniqueness Typing for Functional
Languages with Graph Rewriting Semantics. *Mathematical Structures in
Computer Science*, 6(6):579–612.

Brady, E. (2021). Idris 2: Quantitative Type Theory in Practice.
*European Conference on Object-Oriented Programming (ECOOP)*.

Disselkoen, C., Renner, J., Watt, C., Garber, T., Cauligi, S., and
Stefan, D. (2022). MSWasm: Soundly Enforcing Memory-Safe Execution of
Unsafe Code. *IEEE Symposium on Security and Privacy*.

Elliott, A.S., Ruef, A., Hicks, M., and Tarditi, D. (2018). Checked C:
Making C Safe by Extension. *IEEE Cybersecurity Development (SecDev)*.

Haas, A., Rossberg, A., Schuff, D.L., et al. (2017). Bringing the Web
up to Speed with WebAssembly. *ACM SIGPLAN Conference on Programming
Language Design and Implementation (PLDI)*.

Jewell, J.D.A. (2026). TypedQL: A 10-Level Type Safety Framework for
Database Query Languages. *Technical Report*, hyperpolymath.

Jung, R., Jourdan, J.-H., Krebbers, R., and Dreyer, D. (2018).
RustBelt: Securing the Foundations of the Rust Programming Language.
*Proceedings of the ACM on Programming Languages (POPL)*, 2(POPL):66.

McBride, C. (2016). I Got Plenty o' Nuttin'. *A List of Successes That
Can Change the World*, LNCS 9600:207–233.

Morrisett, G., Walker, D., Crary, K., and Glew, N. (1999). From System F
to Typed Assembly Language. *ACM Transactions on Programming Languages
and Systems*, 21(3):527–568.

Wadler, P. (1990). Linear Types Can Change the World! *Programming
Concepts and Methods*.

Watt, C. (2018). Mechanising and Verifying the WebAssembly
Specification. *ACM SIGPLAN Conference on Certified Programs and Proofs
(CPP)*.

WebAssembly Community Group. (2024a). GC Proposal.
https://github.com/WebAssembly/gc

WebAssembly Community Group. (2024b). Component Model.
https://github.com/WebAssembly/component-model

WebAssembly Community Group. (2024c). WebAssembly Specification.
https://webassembly.github.io/spec/

Würthinger, T., Wimmer, C., Humer, C., et al. (2017). Practical Partial
Evaluation for High-Performance Dynamic Language Runtimes. *ACM SIGPLAN
Conference on Programming Language Design and Implementation (PLDI)*.

---

*typed-wasm is part of the hyperpolymath TypeLL ecosystem.*
*Repository: https://github.com/hyperpolymath/typed-wasm*
