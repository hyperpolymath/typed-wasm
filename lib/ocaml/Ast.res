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

// ============================================================================
// Region Declarations (Section 2 of grammar)
// ============================================================================

/// A region declaration: `region Name[count] { fields; align N; invariant { ... } }`
and regionDecl = {
  name: string,
  instanceCount: option<located<expr>>,
  fields: array<located<fieldDecl>>,
  alignment: option<int>,
  invariants: array<located<invariantExpr>>,
}

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
  effects: option<array<located<effect>>>,
  lifetimeConstraints: array<located<lifetimeConstraint>>,
  body: array<located<statement>>,
}

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
