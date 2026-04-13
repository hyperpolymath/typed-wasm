// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Ast.res — Abstract Syntax Tree for typed-wasm (.twasm) programs.
//
// This module defines the typed AST that the parser produces from tokenised
// source text. The AST mirrors the grammar in spec/grammar.ebnf.
//
// Every node carries a source location (loc) for error reporting.

/// Source location.
type loc = Lexer.loc

/// Located AST node.
type located<'a> = {
  node: 'a,
  loc: loc,
}

// ============================================================================
// Top-Level Declarations
// ============================================================================

/// A typed-wasm module: a list of top-level declarations.
type rec module_ = {
  declarations: array<located<declaration>>,
}

/// Top-level declaration.
and declaration =
  | RegionDecl(regionDecl)
  | ImportRegionDecl(importRegionDecl)
  | ExportRegionDecl(exportRegionDecl)
  | FunctionDecl(functionDecl)
  | MemoryDecl(memoryDecl)
  | InvariantDecl(invariantDecl)
  | ConstDecl(constDecl) // v1.1: top-level `const name : type = literal;`
  | ModuleIsolatedDecl(moduleIsolatedDecl) // v1.2 / L13
  | BoundaryDecl(boundaryDecl) // v1.2 / L13 — only legal inside a ModuleIsolatedDecl body
  | SessionDecl(sessionDecl) // v1.3 / L14
  | CapabilityDecl(capabilityDecl) // v1.4 / L15
  | ChoreographyDecl(choreographyDecl) // v1.5 / L16

// ============================================================================
// v1.2 / L13 — Module Isolation
// ============================================================================
//
// Surface:
//
//   module Renderer isolated {
//       private_memory gfx_mem { initial: 2; maximum: 8; }
//       boundary player_in : import region PlayerState;
//       boundary frame_out : export region RenderedFrame;
//       // ... regular declarations here: regions, functions, ...
//   }
//
// Semantics:
//   * Each isolated module owns AT MOST ONE `private_memory`. Other modules
//     cannot reach into that memory except through a declared `boundary`.
//   * Boundary names are local to their module and must be unique inside
//     the module body (Checker.l13ModuleIsolation).
//   * Boundaries declared OUTSIDE an isolated module body are a parse error:
//     `boundary` only has meaning inside the `module Name isolated { ... }`
//     block. The parser produces a BoundaryDecl-at-top-level error for the
//     top-level occurrence.
//   * An isolated module's body may contain any normal declaration
//     (RegionDecl, FunctionDecl, ImportRegionDecl, ExportRegionDecl,
//     ConstDecl, MemoryDecl, InvariantDecl) plus its nested boundary decls
//     and at most one private_memory.
//
// Reserved-keyword policy:
//   `module`, `isolated`, `private_memory`, `boundary` are NOT globally
//   lexed as keywords (see Lexer.res — contextual reservation). The parser
//   recognises them in context inside parseDeclaration / parseIsolatedBody.

/// v1.2 / L13 — declaration of an isolated module.
and moduleIsolatedDecl = {
  name: string,
  privateMemory: option<located<privateMemoryDecl>>,
  declarations: array<located<declaration>>,
}

/// v1.2 / L13 — private linear-memory declaration inside an isolated module.
///
/// Syntactically similar to a top-level `memory { ... }` declaration but
/// tagged PRIVATE. The checker enforces that private memory is only referenced
/// by regions and placements inside the owning module.
and privateMemoryDecl = {
  name: string,
  initialPages: int,
  maximumPages: option<int>,
}

/// v1.2 / L13 — cross-module boundary declaration.
///
/// A boundary is the ONLY legal path for cross-module region access. It
/// names a boundary (the lookup key), a direction, and the region that
/// is exposed through it.
///
/// Example:
///   boundary player_in : import region PlayerState;
///
/// Semantics:
///   * `import` direction: this module consumes `PlayerState` from another
///     module. The checker pairs this with a matching `export` boundary on
///     the peer side at link time.
///   * `export` direction: this module exposes `regionName` to other modules
///     through this boundary.
and boundaryDecl = {
  name: string,
  direction: boundaryDirection,
  regionName: string,
}

and boundaryDirection =
  | BoundaryImport
  | BoundaryExport

// ============================================================================
// v1.3 / L14 — Session Protocols
// ============================================================================
//
// Surface:
//
//   session OrderFlow {
//       state Idle    : i32;
//       state Pending : i64;
//       state Done    : i32;
//       transition submit  : consume Idle    -> yield Pending;
//       transition approve : consume Pending -> yield Done;
//       dual : OrderFlowDual;
//   }
//
// Semantics:
//   * Each `state` declares a typed-state label optionally annotated with a
//     payload field type. State names must be unique inside a session
//     (Checker L14-A).
//   * Each `transition` consumes a source state and yields a target state.
//     Both source and target MUST be declared `state`s of the same session
//     (Checker L14-B). Transition names need not be unique — same name can
//     appear from different source states (overloaded transitions).
//   * The optional `dual` clause names the peer protocol used by the OTHER
//     party in a two-party session. Symmetry checking (A.dual = B AND
//     B.dual = A) is best-effort at v1.3 — it requires whole-program
//     visibility, so the surface checker only verifies that the named
//     protocol exists in the same module if it does, and otherwise records
//     it for L16 link-time checking.
//
// Reserved-keyword policy: `session`, `state`, `transition`, `consume`,
// `dual` are NOT globally lexed. They arrive as Ident(...) and are
// recognised contextually inside `parseSessionDecl`. The pre-existing
// global `Yield` token (used by v1.1 block-if expressions) is reused
// inside transitions — same token, different surface position.

/// v1.3 / L14 — declaration of a session protocol.
and sessionDecl = {
  name: string,
  states: array<located<sessionStateDecl>>,
  transitions: array<located<sessionTransitionDecl>>,
  dualName: option<string>,
}

/// v1.3 / L14 — typed state declaration inside a session.
///
///   state Idle : i32;
///
/// `payload` is optional; a payload-less state is unit-like and the field
/// type defaults to `i32` (matching the L10 LinHandle inner schema).
and sessionStateDecl = {
  name: string,
  payload: option<located<fieldType>>,
}

/// v1.3 / L14 — transition declaration inside a session.
///
///   transition submit : consume Idle -> yield Pending;
///
/// Surface obligation: both `consumes` and `produces` must name a
/// state declared in the same session block.
and sessionTransitionDecl = {
  name: string,
  consumes: string,
  produces: string,
}

// ============================================================================
// v1.4 / L15 — Resource Capabilities
// ============================================================================
//
// Surface:
//
//   capability read_file;
//   capability web_fetch;
//
//   fn load_config() -> i32 effects {
//       memory: { Read },
//       caps:   { read_file }
//   } { ... }
//
// A `capability NAME;` declaration names an external resource that functions
// in the same module may require via the `caps:` sub-clause of their split
// effects. The v1.1 surface sugar already parses the `caps:` sub-clause into
// `functionDecl.caps`; v1.4 / L15 makes it load-bearing by requiring every
// name in any function's `caps:` set to correspond to a declared
// `capability`, and by enforcing uniqueness of the declarations themselves.
//
// Semantics (checker obligations in Checker.checkCapabilities):
//   * L15-A (Distinct)    : no two `capability` declarations in the same
//                           module (top-level module body OR the body of
//                           a single `ModuleIsolatedDecl`) may share a
//                           name.
//   * L15-B (Well-scoped) : for every `FunctionDecl` with a non-None
//                           `caps` field, every capability name in that
//                           set must refer to a `capability` declaration
//                           in the enclosing module's scope. Inside an
//                           isolated module, "enclosing module" means
//                           that isolated module's declarations; at top
//                           level it means the top-level module.
//
// L15-C (call-graph monotonicity) is proven in the Idris2 core
// (`ResourceCapabilities.idr`: `CallCompatible`, `callCompose`,
// `callReachesModule`) but surface-level call-graph analysis is
// deferred — v1.4 ships without it because the current checker doesn't
// track inter-function calls. When the call-graph check lands, it will
// piggy-back on this same capability-declaration set.
//
// Reserved-keyword policy: `capability` is NOT globally lexed; the parser
// recognises it contextually from `Ident("capability")`. The reserved
// words `grant`, `relinquish`, `requires_caps` remain reserved-but-not-
// live at v1.4 (they are for a future refinement) and the parser rejects
// them at the top level with a pointer to L15+future.

/// v1.4 / L15 — capability declaration.
///
///   capability read_file;
and capabilityDecl = {
  name: string,
}

// ============================================================================
// v1.5 / L16 — Agent Choreography
// ============================================================================
//
// Surface:
//
//   choreography CheckoutFlow {
//     agent_role Buyer  : BuyerSession;
//     agent_role Seller : SellerModule;
//     message pay : Buyer -> Seller, i64;
//     composes: L13 + L14 + L15;
//   }
//
// A choreography declaration composes the already-proven lower levels:
// L13 isolation, L14 session linearity, and L15 capability containment.
// The parser records role/message declarations plus the composition spec;
// Checker.checkChoreography enforces L16-A..L16-D.

/// v1.5 / L16 — choreography declaration.
and choreographyDecl = {
  name: string,
  roles: array<located<agentRoleDecl>>,
  messages: array<located<choreographyMessageDecl>>,
  composition: choreographyCompositionSpec,
}

/// v1.5 / L16 — role declaration in a choreography.
///
///   agent_role RoleName : TargetName;
///
/// `TargetName` must resolve to a session or isolated module in the same file
/// (checked by Checker L16-A).
and agentRoleDecl = {
  roleName: string,
  targetName: string,
}

/// v1.5 / L16 — typed message declaration between roles.
///
///   message MsgName : RoleA -> RoleB, field_type;
///
/// Checker enforces:
///   * from/to roles exist (L16-B)
///   * payload is primitive or declared region reference (L16-C)
and choreographyMessageDecl = {
  name: string,
  fromRole: string,
  toRole: string,
  payload: located<fieldType>,
}

/// v1.5 / L16 — composition spec.
///
/// Current v1.5 surface requires exactly `L13 + L14 + L15`.
/// The parser stores the three components verbatim; checker enforces exact
/// equality so future versions can extend this shape without changing AST.
and choreographyCompositionSpec = {
  first: string,
  second: string,
  third: string,
}

// ============================================================================
// v1.1 — Top-level `const` declaration
// ============================================================================
//
// Surface:
//   const max_hp : i32 = 9999;
//
// Semantics: desugared by downstream consumers into a singleton region
// holding a single field with the declared type and an initializer. The
// checker verifies that `value` is a literal (not a general expression) and
// that the literal's type matches `constType`.

/// Top-level constant binding.
and constDecl = {
  name: string,
  constType: located<fieldType>,
  value: located<expr>, // must be a literal — enforced by Checker.constValueIsLiteral
}

// ============================================================================
// Region Declarations (Section 2 of grammar)
// ============================================================================

/// A region declaration: `region Name[count] [striated] { fields; align N; invariant { ... } }`
and regionDecl = {
  name: string,
  instanceCount: option<located<expr>>,
  layout: regionLayout, // v1.1: AoS (default) or SoA (striated)
  fields: array<located<fieldDecl>>,
  alignment: option<int>,
  invariants: array<located<invariantExpr>>,
}

/// v1.1 region layout — chosen at the schema level, not per access.
///
/// `LayoutAoS` is the pre-v1.1 default: records are contiguous in memory
/// (array-of-structs). Whole-record pointers are allowed.
///
/// `LayoutStriated` is struct-of-arrays: all `field_A` values contiguous,
/// then all `field_B` values contiguous, etc. Whole-record pointers are
/// FORBIDDEN in striated regions because the record's bytes are not
/// contiguous; see Checker.striatedLayoutIsWellFormed. The projection-only
/// rule lets the checker sidestep the AoS/SoA coercion problem entirely.
and regionLayout =
  | LayoutAoS // default — pre-v1.1 behaviour, array-of-structs
  | LayoutStriated // v1.1 — struct-of-arrays, projection-only access

/// A field within a region: `name: type where constraints;`
and fieldDecl = {
  name: string,
  fieldType: located<fieldType>,
  constraints: array<located<constraintExpr>>,
}

/// Field types.
and fieldType =
  | Primitive(primitiveType)
  | RegionRef(string) // @RegionName — embedded region
  | PointerType(pointerKind, located<fieldType>) // ptr<T>, ref<T>, unique<T>
  | OptionalType(located<fieldType>) // opt<T>
  | ArrayFieldType(located<fieldType>, located<expr>) // T[N]
  | UnionType(array<located<variantDecl>>)

/// WASM primitive types.
and primitiveType =
  | I8
  | I16
  | I32
  | I64
  | U8
  | U16
  | U32
  | U64
  | F32
  | F64
  | Bool

/// Pointer kinds.
and pointerKind =
  | PtrOwning // ptr<T> — owning, must free
  | RefBorrow // ref<T> — borrowing, no free
  | UniqueExcl // unique<T> — exclusive owning

/// Union variant.
and variantDecl = {
  tag: string,
  variantType: located<fieldType>,
}

/// Field constraint expressions.
and constraintExpr =
  | RangeConstraint(located<expr>, string, located<expr>) // lo <= field <= hi
  | PredicateConstraint(string, array<located<expr>>)
  | AlignConstraint(int)

/// Region-level invariant expressions.
and invariantExpr = {
  name: string,
  proposition: located<expr>,
}

// ============================================================================
// Import / Export (Section 3 of grammar)
// ============================================================================

/// Import a region from another module.
and importRegionDecl = {
  regionName: string,
  moduleName: string,
  expectedFields: array<located<fieldDecl>>,
}

/// Export a region from this module.
and exportRegionDecl = {
  regionName: string,
}

// ============================================================================
// Functions (Section 4 of grammar)
// ============================================================================

/// Function declaration.
and functionDecl = {
  name: string,
  params: array<located<param>>,
  returnType: option<located<fieldType>>,
  effects: option<array<located<effect>>>, // v1.0 flat effects (memory-only)
  caps: option<array<located<string>>>, // v1.1 split-effects capabilities (names only; opaque in v1.1, checked by L15)
  lifetimeConstraints: array<located<lifetimeConstraint>>,
  body: array<located<statement>>,
}
//
// v1.1 split effects clause — two orthogonal lattices.
//
// The pre-v1.1 flat form `effects { Read, Write, ReadRegion(X) }` remains
// valid and populates only `effects`.
//
// The v1.1 split form `effects { memory: { Read, Write }, caps: { read_file, web_fetch } }`
// populates both `effects` (from `memory:` sub-clause) and `caps` (from
// `caps:` sub-clause). The `caps` set is opaque to v1.1 — the parser accepts
// it and downstream consumers can emit it, but semantic checking of
// capabilities does not activate until L15 (typed-wasm v1.4).
//
// Rationale: emitting the split form from v1.1 means languages targeting
// typed-wasm (007, Ephapax, AffineScript) do not need to regenerate their
// output when the checker upgrades from v1.1 → v1.4. The output is already
// in the final shape; only its semantic enforcement grows.

/// Function parameter.
and param = {
  name: string,
  paramType: located<paramType>,
}

/// Parameter types: either a field type or a region handle type.
and paramType =
  | FieldParam(fieldType)
  | RegionHandleParam(handleMode, string) // &region<Name>, &mut region<Name>, own region<Name>

/// Handle modes for region parameters.
and handleMode =
  | SharedBorrow // &
  | MutableBorrow // &mut
  | Owning // own

/// Memory effects.
and effect =
  | ReadEffect
  | WriteEffect
  | AllocEffect
  | FreeEffect
  | ReadRegionEffect(string)
  | WriteRegionEffect(string)

/// Lifetime constraints.
and lifetimeConstraint = {
  name: string, // lifetime name without the '
  bound: lifetimeBound,
}

/// Lifetime bounds.
and lifetimeBound =
  | StaticLifetime
  | FnLifetime
  | NamedLifetime(string)
  | OutlivesLifetime(string, string) // 'a >= 'b

// ============================================================================
// Statements (Section 5 of grammar)
// ============================================================================

/// Statements within function bodies.
and statement =
  | RegionGetStmt(regionGetStmt)
  | RegionSetStmt(regionSetStmt)
  | RegionScanStmt(regionScanStmt)
  | RegionAllocStmt(regionAllocStmt)
  | RegionFreeStmt(string)
  | LetStmt(letStmt)
  | IfStmt(ifStmt)
  | WhileStmt(whileStmt)
  | ReturnStmt(option<located<expr>>)
  | StaticAssertStmt(located<expr>)
  | ProofStmt(proofStmt)
  | ExprStmt(located<expr>)
  | MatchStmt(matchStmt) // v1.1: match on a tagged-union region field

/// v1.1 match statement — dispatches on the tag of a union-typed region field.
///
/// Surface:
///   match $enemies[i] .kind {
///       | Minion => { ... }
///       | Boss   => { ... }
///       | Shade  => { ... }
///   }
///
/// Semantics: the scrutinee must refer to a field of union type in the region
/// schema; `arms` must be exhaustive with respect to that union's declared
/// variant tags (Checker.matchIsExhaustive). Arms are non-overlapping by
/// construction because each tag may appear at most once.
and matchStmt = {
  target: regionTarget,
  fieldPath: array<fieldPathSegment>,
  arms: array<located<matchArm>>,
}

/// One arm of a v1.1 match statement.
and matchArm = {
  tag: string, // must match a variant tag of the scrutinee's union type
  body: array<located<statement>>,
}

/// region.get $target .field.path -> binding
and regionGetStmt = {
  target: regionTarget,
  fieldPath: array<fieldPathSegment>,
  binding: option<string>,
}

/// region.set $target .field.path, value
and regionSetStmt = {
  target: regionTarget,
  fieldPath: array<fieldPathSegment>,
  value: located<expr>,
}

/// region.scan $target where pred -> |binding| { body }
and regionScanStmt = {
  target: regionTarget,
  predicate: option<located<expr>>,
  bindingName: option<string>,
  body: array<located<statement>>,
}

/// region.alloc RegionName { field = val, ... } -> binding
and regionAllocStmt = {
  regionName: string,
  initializers: array<(string, located<expr>)>,
  binding: string,
}

/// Region target: $name or $name[index]
and regionTarget = {
  name: string,
  index: option<located<expr>>,
}

/// Field path segments: .field or [index]
and fieldPathSegment =
  | FieldAccess(string)
  | IndexAccess(located<expr>)

/// let [mut] name [: type] = expr;
and letStmt = {
  isMutable: bool,
  name: string,
  typeAnnotation: option<located<fieldType>>,
  initializer: located<expr>,
}

/// if expr { stmts } [else { stmts }]
and ifStmt = {
  condition: located<expr>,
  thenBranch: array<located<statement>>,
  elseBranch: option<array<located<statement>>>,
}

/// while expr { stmts }
and whileStmt = {
  condition: located<expr>,
  body: array<located<statement>>,
}

/// proof name { steps }
and proofStmt = {
  name: string,
  steps: array<located<proofStep>>,
}

/// Individual proof step.
and proofStep =
  | GivenStep(located<expr>)
  | ShowStep(located<expr>)
  | ByStep(proofTactic)

/// Proof tactics.
and proofTactic =
  | BoundsCheck
  | Linearity
  | Lifetime
  | AliasFreedom
  | EffectPurity
  | Induction(string)
  | Rewrite(string)

// ============================================================================
// Expressions (Section 6 of grammar)
// ============================================================================

/// Expressions.
and expr =
  | IntLit(int)
  | FloatLit(float)
  | StringLit(string)
  | BoolLit(bool)
  | NullLit
  | Identifier(string)
  | RegionVar(string) // $name
  | BinOp(located<expr>, binOp, located<expr>)
  | UnaryOp(unaryOp, located<expr>)
  | SizeofExpr(string) // sizeof(RegionName)
  | OffsetofExpr(string, string) // offsetof(Region.field)
  | TypeofExpr(located<expr>)
  | IsValidExpr(string) // is_valid($name)
  | IsNullExpr(located<expr>)
  | CastExpr(located<fieldType>, located<expr>) // cast<Type>(expr)
  | ParenExpr(located<expr>)
  | CallExpr(string, array<located<expr>>)
  | BlockIfExpr(blockIfExpr) // v1.1: if cond { stmts; yield e } else { stmts; yield e }

/// v1.1 block-expression if. Distinct from IfStmt (statement form) in that it
/// produces a value, yielded from each branch by the last expression in a
/// `yield`-terminated block. Both branches must yield the same type (checker
/// obligation: Checker.blockIfBranchesAgree).
///
/// Surface:
///   let damage = if boss_phase == 2 { yield 20 } else { yield 10 };
///
/// The branches may contain zero or more statements before the yield; at
/// least one yield is required per branch.
and blockIfExpr = {
  condition: located<expr>,
  thenStmts: array<located<statement>>,
  thenYield: located<expr>,
  elseStmts: array<located<statement>>,
  elseYield: located<expr>,
}

/// Binary operators.
and binOp =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | NotEq
  | Lt
  | Gt
  | LtEq
  | GtEq
  | And
  | Or
  | BitAnd
  | BitOr
  | BitXor
  | Shl
  | Shr

/// Unary operators.
and unaryOp =
  | Neg
  | Not
  | BitNot

// ============================================================================
// Memory Declaration (Section 7 of grammar)
// ============================================================================

/// Memory declaration.
and memoryDecl = {
  name: string,
  initialPages: int,
  maximumPages: option<int>,
  isShared: bool,
  placements: array<located<regionPlacement>>,
}

/// Region placement: `place RegionName at offset;`
and regionPlacement = {
  regionName: string,
  offset: located<expr>,
}

// ============================================================================
// Global Invariant (Section 8 of grammar)
// ============================================================================

/// Cross-region invariant declaration.
and invariantDecl = {
  name: string,
  regions: array<string>,
  proposition: located<expr>,
  proofTactic: option<proofTactic>,
}
