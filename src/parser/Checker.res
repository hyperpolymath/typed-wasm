// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Checker.res — v1.1 post-parse well-formedness checks for typed-wasm.
//
// The parser accepts every grammatically valid program. This module imposes
// the v1.1 semantic obligations that cannot be expressed in the EBNF alone:
//
//   1. constValueIsLiteral
//      A `const` declaration's initializer must be a literal (Int / Float /
//      String / Bool / Null). The parser accepts any expression here to keep
//      the grammar uniform and to leave the door open for a v1.2+ relaxation
//      that allows const-folded expressions.
//
//   2. matchIsExhaustive
//      A `match` statement's arms must cover every declared variant tag of
//      the scrutinee's union-typed field, with no duplicate tags and no
//      unknown tags. The parser produces a MatchStmt AST node regardless of
//      exhaustiveness; this checker rejects non-exhaustive matches with a
//      precise error citing the missing tags.
//
//   3. blockIfBranchesAgree
//      A `BlockIfExpr`'s `thenYield` and `elseYield` must have the same type.
//      v1.1 does not track full expression types post-parse, so this checker
//      performs a STRUCTURAL check: both yield expressions must be the same
//      AST shape (e.g. both literals of the same primitive type, or both
//      region.get projections on the same field path). Richer type agreement
//      lands with a proper type checker in a later version.
//
//   4. striatedLayoutIsWellFormed
//      A `region Foo[N] striated { ... }` declaration must NOT contain any
//      field whose type is a pointer to a whole region (`ptr<@R>`,
//      `unique<@R>`, `ref<@R>`), because striated (SoA) layout means the
//      record's bytes are not contiguous, so whole-record pointers have no
//      meaningful semantics. Field-level pointers to primitive types are
//      allowed. This implements the projection-only rule from
//      typed-wasm/spec/L13-L16-reserved-syntax.adoc → "Striation".
//
// Each check returns either `Ok()` or `Error` carrying a located diagnostic.
// A single top-level `checkModule` runs all four checks across the whole
// module and returns an accumulated error list.
//
// These checks are INTENTIONALLY implemented at the ReScript level (not in
// Idris2) for v1.1. The Idris2 proof core remains the ultimate authority for
// L1-L10 properties; v1.1 sugar checks are fast-fail feedback for consumers
// and are below the "formally proven" bar. They may migrate to Idris2 in a
// later version alongside the L17 "Layout-proof striation" work.

open Ast

// ============================================================================
// Diagnostic type
// ============================================================================

type diagnostic = {
  message: string,
  loc: Lexer.loc,
}

type checkResult<'a> = result<'a, array<diagnostic>>

// ============================================================================
// 1. constValueIsLiteral — const initializer must be a literal
// ============================================================================

/// Returns true if the expression is a literal (one of the leaf Lit
/// constructors). Parenthesised literals are unwrapped transparently.
let rec isLiteral = (e: expr): bool => {
  switch e {
  | IntLit(_) => true
  | FloatLit(_) => true
  | StringLit(_) => true
  | BoolLit(_) => true
  | NullLit => true
  | ParenExpr(inner) => isLiteral(inner.node)
  | _ => false
  }
}

let checkConstDecl = (c: constDecl, loc: Lexer.loc): array<diagnostic> => {
  if isLiteral(c.value.node) {
    []
  } else {
    [
      {
        message: "const `" ++ c.name ++ "` initializer must be a literal " ++
          "(Int / Float / String / Bool / Null). Expression-valued const bindings " ++
          "are not supported in v1.1.",
        loc,
      },
    ]
  }
}

// ============================================================================
// 2. matchIsExhaustive — match arms must cover all union variant tags
// ============================================================================

/// Context threaded through the checker for the current function. Carries
/// the parameter-name → region-name map so that handle parameters
/// (`e: &region<Enemies>`) can be resolved to their underlying region
/// schema when used as match scrutinees (`match $e[i] .field`).
///
/// At module top level (outside any function) the context is empty and
/// only direct-region-name targets (`match $Enemies[0] .field`) resolve.
type functionContext = {
  handleParams: array<(string, string)>, // (paramName, regionName)
}

let emptyContext: functionContext = {handleParams: []}

/// Build a function context from a FunctionDecl. Scans parameters and
/// records any whose type is a `RegionHandleParam(_, RegionName)`.
let buildFunctionContext = (fd: functionDecl): functionContext => {
  let handleParams: array<(string, string)> = []
  Array.forEach(fd.params, p => {
    switch p.node.paramType.node {
    | RegionHandleParam(_, regionName) =>
      let _ = Array.push(handleParams, (p.node.name, regionName))
    | _ => ()
    }
  })
  {handleParams: handleParams}
}

/// Look up a region declaration by name in a module. Returns None if not
/// found (the match statement will emit a separate "unknown region" error
/// in that case).
let findRegion = (m: module_, name: string): option<regionDecl> => {
  // declarations is an array; we linear-scan because v1.1 programs are
  // small. If this becomes hot in v1.2+, replace with a hash table.
  let found = ref(None)
  Array.forEach(m.declarations, decl => {
    switch decl.node {
    | RegionDecl(r) if r.name == name =>
      if found.contents == None {
        found := Some(r)
      }
    | _ => ()
    }
  })
  found.contents
}

/// Walk the field path from the region's top-level fields and return the
/// located<fieldType> of the final field, or None if any segment doesn't
/// resolve. Array indexing (`[expr]`) strips one array layer.
let rec resolveFieldPath = (
  region: regionDecl,
  path: array<fieldPathSegment>,
): option<fieldType> => {
  if Array.length(path) == 0 {
    None
  } else {
    let first = path->Array.getUnsafe(0)
    switch first {
    | FieldAccess(fname) =>
      // Find the top-level field
      let field = ref(None)
      Array.forEach(region.fields, f => {
        if f.node.name == fname && field.contents == None {
          field := Some(f.node.fieldType.node)
        }
      })
      switch field.contents {
      | None => None
      | Some(ft) =>
        let rest = Array.sliceToEnd(path, ~start=1)
        resolveFurtherFieldPath(ft, rest)
      }
    | IndexAccess(_) => None // Index at the head has no field to resolve
    }
  }
}

/// Continue walking a field path from a field type we already resolved.
/// This version descends into union/primitive/embedded-region types.
and resolveFurtherFieldPath = (ft: fieldType, path: array<fieldPathSegment>): option<fieldType> => {
  if Array.length(path) == 0 {
    Some(ft)
  } else {
    let first = path->Array.getUnsafe(0)
    switch first {
    | IndexAccess(_) =>
      // Array element access: strip one layer of ArrayFieldType
      switch ft {
      | ArrayFieldType(inner, _) =>
        resolveFurtherFieldPath(inner.node, Array.sliceToEnd(path, ~start=1))
      | _ => None
      }
    | FieldAccess(_) =>
      // v1.1 doesn't track enough schema info to chase fields inside
      // primitives or non-union types. For the exhaustiveness check we
      // only need to find a union at the END of the path, so if we land
      // here before exhausting the path we bail out conservatively.
      Some(ft)
    }
  }
}

/// Extract the variant tags from a union field type, if it is one.
let extractUnionVariants = (ft: fieldType): option<array<string>> => {
  switch ft {
  | UnionType(variants) =>
    Some(variants->Array.map(v => v.node.tag))
  | _ => None
  }
}

/// Resolve a match target to its underlying region declaration. First
/// tries direct lookup by name (singleton regions used without a handle,
/// e.g. `match $Enemies .kind`). If that fails and we have a function
/// context, tries handle-parameter lookup (`e: &region<Enemies>` →
/// `Enemies`). Returns None if neither resolves.
let resolveTargetToRegion = (
  ctx: functionContext,
  m: module_,
  targetName: string,
): option<regionDecl> => {
  switch findRegion(m, targetName) {
  | Some(r) => Some(r)
  | None =>
    let resolvedName = ref(None)
    Array.forEach(ctx.handleParams, ((paramName, regionName)) => {
      if paramName == targetName && resolvedName.contents == None {
        resolvedName := Some(regionName)
      }
    })
    switch resolvedName.contents {
    | Some(rn) => findRegion(m, rn)
    | None => None
    }
  }
}

let checkMatchStmt = (
  ctx: functionContext,
  m: module_,
  ms: matchStmt,
  loc: Lexer.loc,
): array<diagnostic> => {
  let diags: array<diagnostic> = []
  let targetName = ms.target.name

  switch resolveTargetToRegion(ctx, m, targetName) {
  | None =>
    // The region itself does not exist. Emit a direct error — the checker
    // catches this before the exhaustiveness check would complain about
    // "no union variants".
    let _ = Array.push(
      diags,
      {
        message: "match on unknown region `" ++ targetName ++ "`",
        loc,
      },
    )
    diags
  | Some(region) =>
    switch resolveFieldPath(region, ms.fieldPath) {
    | None =>
      let _ = Array.push(
        diags,
        {
          message: "match scrutinee does not resolve to a known field of region `" ++
            targetName ++ "`",
          loc,
        },
      )
      diags
    | Some(ft) =>
      switch extractUnionVariants(ft) {
      | None =>
        let _ = Array.push(
          diags,
          {
            message: "match scrutinee must be a union-typed field; got a non-union field type",
            loc,
          },
        )
        diags
      | Some(variants) =>
        // Check each arm's tag is in the variant set, track coverage, and
        // flag duplicates and unknowns.
        let covered: array<string> = []
        let seen: array<string> = []
        Array.forEach(ms.arms, arm => {
          let tag = arm.node.tag
          let isKnown = Array.includes(variants, tag)
          let isDup = Array.includes(seen, tag)
          if !isKnown {
            let _ = Array.push(
              diags,
              {
                message: "match arm `" ++ tag ++
                  "` is not a declared variant of the scrutinee's union",
                loc: arm.loc,
              },
            )
          }
          if isDup {
            let _ = Array.push(
              diags,
              {
                message: "duplicate match arm for variant `" ++ tag ++ "`",
                loc: arm.loc,
              },
            )
          }
          let _ = Array.push(seen, tag)
          if isKnown && !isDup {
            let _ = Array.push(covered, tag)
          }
        })
        // Check exhaustiveness: every declared variant must be covered.
        let missing = variants->Array.filter(v => !Array.includes(covered, v))
        if Array.length(missing) > 0 {
          let _ = Array.push(
            diags,
            {
              message: "non-exhaustive match: missing variant(s) " ++
                missing->Array.joinWith(", "),
              loc,
            },
          )
        }
        diags
      }
    }
  }
}

// ============================================================================
// 3. blockIfBranchesAgree — both yields must have the same structural shape
// ============================================================================

/// A coarse structural tag for a yield expression, used to compare
/// thenYield and elseYield without a full type checker. v1.1 catches
/// obvious mismatches (e.g. `yield 42` vs `yield "foo"`) and recursively
/// descends into nested forms so a nested block-if is compared against
/// whatever its leaf yield produces, not against the opaque `BlockIf`
/// tag. Richer type agreement lands with a proper v1.2 type checker.
///
/// Opaque forms (Identifier, RegionVar, Call, Sizeof, …) all land under
/// the neutral "Value" tag because v1.1 cannot resolve their types
/// without symbol resolution. This means `yield x` and `yield y` match
/// even if x and y are different types — a deliberate weakening so the
/// Checker is not confused by variables of unknown type.
let rec yieldShapeTag = (e: expr): string => {
  switch e {
  | IntLit(_) => "Int"
  | FloatLit(_) => "Float"
  | StringLit(_) => "String"
  | BoolLit(_) => "Bool"
  | NullLit => "Null"
  // Identifier / RegionVar / Call / introspection forms all have type
  // information the v1.1 checker cannot yet resolve — treat as a neutral
  // "Value" tag so same-side mismatches do not spuriously fire.
  | Identifier(_) => "Value"
  | RegionVar(_) => "Value"
  | SizeofExpr(_) => "Value"
  | OffsetofExpr(_, _) => "Value"
  | TypeofExpr(_) => "Value"
  | IsValidExpr(_) => "Value"
  | CallExpr(_, _) => "Value"
  // Boolean-producing forms all land under "Bool" so `yield (a == b)`
  // matches `yield true`.
  | IsNullExpr(_) => "Bool"
  // Arithmetic/logical binops are numeric unless short-circuit Bool ops,
  // which are caught separately.
  | BinOp(_, And, _) => "Bool"
  | BinOp(_, Or, _)  => "Bool"
  | BinOp(_, _, _)   => "Value" // numeric; opaque at v1.1
  | UnaryOp(Not, _)  => "Bool"
  | UnaryOp(_, _)    => "Value"
  | CastExpr(_, _) => "Value"
  // Unwrap transparent wrappers recursively.
  | ParenExpr(inner) => yieldShapeTag(inner.node)
  | BlockIfExpr(b) =>
    // Recurse into the branch yields: a block-if's shape is the shape of
    // its then-branch (which must agree with its else-branch by the same
    // check on the nested block-if). This lets nested block-ifs compose.
    yieldShapeTag(b.thenYield.node)
  }
}

let checkBlockIfExpr = (b: blockIfExpr, loc: Lexer.loc): array<diagnostic> => {
  let thenTag = yieldShapeTag(b.thenYield.node)
  let elseTag = yieldShapeTag(b.elseYield.node)
  if thenTag == elseTag {
    []
  } else {
    [
      {
        message: "block-if branches yield different shapes: then = " ++ thenTag ++
          ", else = " ++ elseTag ++
          ". v1.1 requires structural agreement; richer type agreement lands in a later version.",
        loc,
      },
    ]
  }
}

// ============================================================================
// 4. striatedLayoutIsWellFormed — no whole-record pointers in striated regions
// ============================================================================

/// Is this field type a whole-record pointer that would break under SoA
/// (striated) layout? Pointer-to-primitive is fine because the element
/// type is not spread across stripes. Pointer-to-embedded-region (@R) is
/// NOT fine because the embedded region IS a composite record.
let isWholeRecordPointer = (ft: fieldType): bool => {
  switch ft {
  | PointerType(_, innerLocated) =>
    switch innerLocated.node {
    | RegionRef(_) => true // ptr<@R> / unique<@R> / ref<@R>
    | _ => false
    }
  | _ => false
  }
}

let checkStriatedRegion = (r: regionDecl, loc: Lexer.loc): array<diagnostic> => {
  switch r.layout {
  | LayoutAoS => [] // no constraint
  | LayoutStriated =>
    let diags: array<diagnostic> = []
    Array.forEach(r.fields, f => {
      if isWholeRecordPointer(f.node.fieldType.node) {
        let _ = Array.push(
          diags,
          {
            message: "striated region `" ++ r.name ++
              "` may not contain whole-record pointer field `" ++
              f.node.name ++
              "`. Striated (SoA) layout spreads each record across stripes, so " ++
              "whole-record pointers have no contiguous target. Use projection-only " ++
              "access (region.get / region.set), or switch the region to AoS. See " ++
              "typed-wasm/spec/L13-L16-reserved-syntax.adoc → Striation.",
            loc: f.loc,
          },
        )
      }
    })
    if Array.length(diags) == 0 {
      []
    } else {
      // Also emit a top-level message on the region itself pointing at the
      // first offending field.
      let _ = Array.push(
        diags,
        {
          message: "striated region `" ++ r.name ++ "` is not well-formed: see field error(s) above",
          loc,
        },
      )
      diags
    }
  }
}

// ============================================================================
// 5. l13ModuleIsolation — v1.2 L13 well-formedness
// ============================================================================
//
// L13 introduces isolated modules with private memory and declared boundaries.
// The Idris2-side correctness story lives in
// TypedWasm/ABI/ModuleIsolation.idr; this ReScript checker enforces the
// *surface*-level obligations that drop out to diagnostics instead of proof
// failures:
//
//   L13-A  Boundary names inside a single isolated module must be unique.
//   L13-B  An isolated module must not contain a top-level `memory { ... }`
//          declaration — private memory is declared with `private_memory`
//          instead, and mixing the two inside one isolated module is a
//          configuration smell that the checker catches early.
//   L13-C  An isolated module's export boundaries must name a region that
//          exists as a RegionDecl in the same module body. An import
//          boundary's region is external and therefore not checked here.
//   L13-D  Stray boundary / private_memory decls at the top level were
//          already rejected at parse time (Parser.parseDeclaration). This
//          check does not need to re-verify it.
//
// These obligations live here — not in Idris2 — because they are
// source-surface issues. The Idris2 proof file states the semantic
// invariant (access requires boundary witness or local-ownership); this
// checker prevents obviously-malformed surface input from ever reaching it.

/// Collect the L13-A / L13-B / L13-C diagnostics for one isolated module.
let checkIsolatedModule = (im: moduleIsolatedDecl, loc: Lexer.loc): array<diagnostic> => {
  let diags: array<diagnostic> = []

  // L13-A: unique boundary names inside this module body.
  let seenBoundaryNames: array<string> = []
  // L13-C: collect region names declared in this module's body.
  let declaredRegions: array<string> = []
  // L13-B: detect top-level memory decls INSIDE the isolated body.
  Array.forEach(im.declarations, d => {
    switch d.node {
    | BoundaryDecl(b) =>
      if Array.includes(seenBoundaryNames, b.name) {
        let _ = Array.push(
          diags,
          {
            message: "duplicate boundary name '" ++
            b.name ++
            "' inside isolated module '" ++
            im.name ++ "' (L13 requires boundary names be unique per module)",
            loc: d.loc,
          },
        )
      } else {
        let _ = Array.push(seenBoundaryNames, b.name)
      }
    | RegionDecl(r) =>
      let _ = Array.push(declaredRegions, r.name)
    | MemoryDecl(_) =>
      let _ = Array.push(
        diags,
        {
          message: "isolated module '" ++
          im.name ++
          "' may not declare a top-level 'memory' block; use 'private_memory' instead (L13)",
          loc: d.loc,
        },
      )
    | _ => ()
    }
  })

  // L13-C: every export boundary must name a locally-declared region.
  Array.forEach(im.declarations, d => {
    switch d.node {
    | BoundaryDecl(b) =>
      switch b.direction {
      | BoundaryExport =>
        if !Array.includes(declaredRegions, b.regionName) {
          let _ = Array.push(
            diags,
            {
              message: "export boundary '" ++
              b.name ++
              "' references region '" ++
              b.regionName ++
              "' which is not declared inside isolated module '" ++
              im.name ++ "' (L13 — export boundaries must be locally-defined)",
              loc: d.loc,
            },
          )
        }
      | BoundaryImport => () // import regions live in another module; not checked here
      }
    | _ => ()
    }
  })

  // Silence the unused-loc warning: keep the loc parameter for future
  // "module declaration itself has a problem" diagnostics.
  let _ = loc
  diags
}

// ============================================================================
// 6. checkSession — v1.3 L14 well-formedness
// ============================================================================
//
// L14 introduces session protocols whose surface bugs the Idris2 proof
// (TypedWasm/ABI/SessionProtocol.idr) cannot catch alone, because the proof
// works on already-built Protocol records. This checker handles the
// surface obligations:
//
//   L14-A  State names must be unique inside a single session.
//   L14-B  Every transition's `consumes` and `produces` MUST refer to a
//          state declared in the SAME session block. (TransitionsClosed
//          on the Idris2 side; surface diagnostic here so users get a
//          source location instead of a proof obligation.)
//   L14-C  Transition names need not be unique (overloading is allowed),
//          but a transition CANNOT have the same source-and-target state
//          as another transition with the same name (would prevent
//          overload resolution). The current check is a stricter "no
//          duplicate (name, consumes) pairs" rule.
//   L14-D  If `dual : OtherProto` is declared and `OtherProto` is also
//          declared in the same module, then `OtherProto.dual` must
//          name THIS session in return — symmetry. If `OtherProto` is not
//          declared in this module, the dual is recorded for L16
//          link-time checking and no diagnostic fires here.

let checkSession = (s: sessionDecl, m: module_, loc: Lexer.loc): array<diagnostic> => {
  let diags: array<diagnostic> = []

  // L14-A: collect state names, flag duplicates.
  let seenStateNames: array<string> = []
  Array.forEach(s.states, st => {
    if Array.includes(seenStateNames, st.node.name) {
      let _ = Array.push(
        diags,
        {
          message: "duplicate state name '" ++
          st.node.name ++
          "' inside session '" ++
          s.name ++ "' (L14-A)",
          loc: st.loc,
        },
      )
    } else {
      let _ = Array.push(seenStateNames, st.node.name)
    }
  })

  // L14-B: every transition references declared states.
  Array.forEach(s.transitions, t => {
    if !Array.includes(seenStateNames, t.node.consumes) {
      let _ = Array.push(
        diags,
        {
          message: "transition '" ++
          t.node.name ++
          "' in session '" ++
          s.name ++
          "' consumes undeclared state '" ++
          t.node.consumes ++ "' (L14-B)",
          loc: t.loc,
        },
      )
    }
    if !Array.includes(seenStateNames, t.node.produces) {
      let _ = Array.push(
        diags,
        {
          message: "transition '" ++
          t.node.name ++
          "' in session '" ++
          s.name ++
          "' produces undeclared state '" ++
          t.node.produces ++ "' (L14-B)",
          loc: t.loc,
        },
      )
    }
  })

  // L14-C: no duplicate (name, consumes) pairs.
  let seenPairs: array<string> = []
  Array.forEach(s.transitions, t => {
    let key = t.node.name ++ "@" ++ t.node.consumes
    if Array.includes(seenPairs, key) {
      let _ = Array.push(
        diags,
        {
          message: "duplicate transition '" ++
          t.node.name ++
          "' from state '" ++
          t.node.consumes ++
          "' in session '" ++
          s.name ++ "' (L14-C)",
          loc: t.loc,
        },
      )
    } else {
      let _ = Array.push(seenPairs, key)
    }
  })

  // L14-D: dual symmetry — best-effort, intra-module only.
  switch s.dualName {
  | Some(other) =>
    // Find `other` as a SessionDecl in the same module.
    let foundDual = ref(None)
    Array.forEach(m.declarations, d => {
      switch d.node {
      | SessionDecl(o) =>
        if o.name == other {
          foundDual := Some(o)
        }
      | _ => ()
      }
    })
    switch foundDual.contents {
    | Some(o) =>
      switch o.dualName {
      | Some(back) =>
        if back != s.name {
          let _ = Array.push(
            diags,
            {
              message: "dual asymmetry: session '" ++
              s.name ++
              "' declares dual = '" ++
              other ++
              "', but '" ++
              other ++
              "' declares dual = '" ++ back ++ "' (L14-D)",
              loc,
            },
          )
        }
      | None =>
        let _ = Array.push(
          diags,
          {
            message: "dual asymmetry: session '" ++
            s.name ++
            "' declares dual = '" ++
            other ++
            "', but '" ++
            other ++ "' has no dual clause (L14-D)",
            loc,
          },
        )
      }
    | None => () // out-of-module dual — deferred to L16 link-time
    }
  | None => ()
  }

  diags
}

// ============================================================================
// 7. checkCapabilities — v1.4 L15 well-formedness
// ============================================================================
//
// L15 makes the v1.1 `caps:` sub-clause load-bearing. Each module (top-level
// or isolated) declares a capability set via `capability NAME;` declarations,
// and every function inside that module whose split-effects clause carries
// a `caps: { ... }` sub-list must only name capabilities that are declared
// in the enclosing module's scope.
//
//   L15-A  (Distinct)     Within one module body, no two `capability` decls
//                         may share a name.
//   L15-B  (Well-scoped)  A function's `caps: { ... }` set must be a subset
//                         of the enclosing module's declared capability set.
//
// The Idris2 proof `ResourceCapabilities.idr` carries the full soundness
// story (call-graph monotonicity L15-C via `CallCompatible` + `callCompose`).
// Surface call-graph analysis is deferred — v1.4 ships L15-A + L15-B only
// because the current checker does not track inter-function calls.
//
// "Enclosing module" follows the same scoping as L13: inside a
// `ModuleIsolatedDecl` body, the enclosing module is that isolated module's
// declarations; at top level, it is the top-level module. Capability sets
// from different isolated modules are disjoint.

/// Collect the set of capability names declared in a flat declaration list.
/// Returns (names, diagnostics): the accumulated name list and any L15-A
/// duplicate diagnostics. Only top-level CapabilityDecls are considered —
/// capabilities declared inside a nested isolated module are the inner
/// module's concern, not the outer one's (they are scoped independently).
let collectCapabilitiesInScope = (
  decls: array<Ast.located<Ast.declaration>>,
  scopeLabel: string,
): (array<string>, array<diagnostic>) => {
  let names: array<string> = []
  let diags: array<diagnostic> = []
  Array.forEach(decls, d => {
    switch d.node {
    | CapabilityDecl(c) =>
      if Array.includes(names, c.name) {
        let _ = Array.push(
          diags,
          {
            message: "duplicate capability '" ++
            c.name ++
            "' in " ++
            scopeLabel ++ " (L15-A: capability declarations must be distinct within a module)",
            loc: d.loc,
          },
        )
      } else {
        let _ = Array.push(names, c.name)
      }
    | _ => ()
    }
  })
  (names, diags)
}

/// Check a function declaration's `caps:` sub-clause against the enclosing
/// module's declared capability set. Emits one L15-B diagnostic per
/// unscoped capability name.
let checkFunctionCapsScoped = (
  fd: Ast.functionDecl,
  enclosingCaps: array<string>,
  scopeLabel: string,
  fdLoc: Lexer.loc,
): array<diagnostic> => {
  let diags: array<diagnostic> = []
  switch fd.caps {
  | None => () // flat effects form; L15-B does not apply
  | Some(caps) =>
    Array.forEach(caps, capEntry => {
      if !Array.includes(enclosingCaps, capEntry.node) {
        let _ = Array.push(
          diags,
          {
            message: "function '" ++
            fd.name ++
            "' requires capability '" ++
            capEntry.node ++
            "' which is not declared in " ++
            scopeLabel ++
            " (L15-B: add `capability " ++
            capEntry.node ++ ";` to the enclosing module)",
            loc: capEntry.loc,
          },
        )
      }
    })
  }
  let _ = fdLoc
  diags
}

// ============================================================================
// 8. checkChoreography — v1.5 L16 well-formedness
// ============================================================================
//
// L16 choreography declarations compose lower-level obligations. Surface checks:
//
//   L16-A  Each `agent_role` target must name a session OR isolated module
//          declared in the same file.
//   L16-B  Each message endpoint (`from` / `to`) must name a declared role in
//          the choreography.
//   L16-C  Message payload type must be primitive OR a declared region
//          reference (`@RegionName`) in the same file.
//   L16-D  Composition spec must be exactly `L13 + L14 + L15` at v1.5.

let pushUnique = (names: array<string>, name: string): unit => {
  if !Array.includes(names, name) {
    let _ = Array.push(names, name)
  }
}

let rec collectSessionNamesInDecls = (
  decls: array<Ast.located<Ast.declaration>>,
  acc: array<string>,
): unit => {
  Array.forEach(decls, d => {
    switch d.node {
    | SessionDecl(s) => pushUnique(acc, s.name)
    | ModuleIsolatedDecl(im) => collectSessionNamesInDecls(im.declarations, acc)
    | _ => ()
    }
  })
}

let rec collectIsolatedModuleNamesInDecls = (
  decls: array<Ast.located<Ast.declaration>>,
  acc: array<string>,
): unit => {
  Array.forEach(decls, d => {
    switch d.node {
    | ModuleIsolatedDecl(im) =>
      pushUnique(acc, im.name)
      collectIsolatedModuleNamesInDecls(im.declarations, acc)
    | _ => ()
    }
  })
}

let rec collectRegionNamesInDecls = (
  decls: array<Ast.located<Ast.declaration>>,
  acc: array<string>,
): unit => {
  Array.forEach(decls, d => {
    switch d.node {
    | RegionDecl(r) => pushUnique(acc, r.name)
    | ModuleIsolatedDecl(im) => collectRegionNamesInDecls(im.declarations, acc)
    | _ => ()
    }
  })
}

let checkChoreography = (
  c: Ast.choreographyDecl,
  m: module_,
  loc: Lexer.loc,
): array<diagnostic> => {
  let diags: array<diagnostic> = []

  // Collect declaration sets from the full file (top-level + nested isolated).
  let sessionNames: array<string> = []
  let isolatedModuleNames: array<string> = []
  let regionNames: array<string> = []
  collectSessionNamesInDecls(m.declarations, sessionNames)
  collectIsolatedModuleNamesInDecls(m.declarations, isolatedModuleNames)
  collectRegionNamesInDecls(m.declarations, regionNames)

  // L16-A: role targets must resolve to a declared session or isolated module.
  Array.forEach(c.roles, r => {
    let target = r.node.targetName
    let foundSession = Array.includes(sessionNames, target)
    let foundModule = Array.includes(isolatedModuleNames, target)
    if !foundSession && !foundModule {
      let _ = Array.push(
        diags,
        {
          message: "agent_role '" ++
          r.node.roleName ++
          "' references '" ++
          target ++
          "' which is not a declared session or isolated module in this file (L16-A)",
          loc: r.loc,
        },
      )
    }
  })

  let roleNames = c.roles->Array.map(r => r.node.roleName)

  // L16-B + L16-C: message endpoints and payload typing constraints.
  Array.forEach(c.messages, msgDecl => {
    let msg = msgDecl.node
    if !Array.includes(roleNames, msg.fromRole) {
      let _ = Array.push(
        diags,
        {
          message: "message '" ++
          msg.name ++
          "' references unknown from-role '" ++
          msg.fromRole ++ "' (L16-B)",
          loc: msgDecl.loc,
        },
      )
    }
    if !Array.includes(roleNames, msg.toRole) {
      let _ = Array.push(
        diags,
        {
          message: "message '" ++
          msg.name ++
          "' references unknown to-role '" ++
          msg.toRole ++ "' (L16-B)",
          loc: msgDecl.loc,
        },
      )
    }
    switch msg.payload.node {
    | Primitive(_) => ()
    | RegionRef(regionName) =>
      if !Array.includes(regionNames, regionName) {
        let _ = Array.push(
          diags,
          {
            message: "message '" ++
            msg.name ++
            "' payload references undeclared region '" ++
            regionName ++ "' (L16-C)",
            loc: msg.payload.loc,
          },
        )
      }
    | _ =>
      let _ = Array.push(
        diags,
        {
          message: "message '" ++
          msg.name ++
          "' payload type is not allowed in v1.5 choreography: use a primitive or declared region reference (L16-C)",
          loc: msg.payload.loc,
        },
      )
    }
  })

  // L16-D: composition spec fixed to L13 + L14 + L15 at v1.5.
  if c.composition.first != "L13" || c.composition.second != "L14" || c.composition.third != "L15" {
    let _ = Array.push(
      diags,
      {
        message: "choreography '" ++
        c.name ++
        "' must declare `composes: L13 + L14 + L15;` at v1.5 (L16-D)",
        loc,
      },
    )
  }

  diags
}

// ============================================================================
// Top-level module check — runs all checks, returns accumulated diags
// ============================================================================

/// Recursively walk a function body (and its nested if/while/match arms)
/// collecting block-if and match-stmt diagnostics. The `ctx` parameter
/// carries the enclosing function's handle-parameter map so that match
/// scrutinees can resolve handle parameters to their declared regions.
let rec walkStatements = (
  ctx: functionContext,
  m: module_,
  stmts: array<Ast.located<statement>>,
  acc: array<diagnostic>,
): array<diagnostic> => {
  Array.forEach(stmts, s => {
    switch s.node {
    | MatchStmt(ms) =>
      let d = checkMatchStmt(ctx, m, ms, s.loc)
      Array.forEach(d, x => {
        let _ = Array.push(acc, x)
      })
      // Walk each arm body
      Array.forEach(ms.arms, arm => {
        let _ = walkStatements(ctx, m, arm.node.body, acc)
      })
    | IfStmt(ifs) =>
      // Walk expression for block-if (statement-form ifs never contain block-if
      // since block-if is expression-position only, but the condition may
      // contain one)
      let _ = walkExpr(ifs.condition, acc)
      let _ = walkStatements(ctx, m, ifs.thenBranch, acc)
      switch ifs.elseBranch {
      | Some(eb) =>
        let _ = walkStatements(ctx, m, eb, acc)
      | None => ()
      }
    | WhileStmt(ws) =>
      let _ = walkExpr(ws.condition, acc)
      let _ = walkStatements(ctx, m, ws.body, acc)
    | LetStmt(ls) =>
      let _ = walkExpr(ls.initializer, acc)
    | ReturnStmt(Some(e)) =>
      let _ = walkExpr(e, acc)
    | RegionSetStmt(rs) =>
      let _ = walkExpr(rs.value, acc)
    | ExprStmt(e) =>
      let _ = walkExpr(e, acc)
    | StaticAssertStmt(e) =>
      let _ = walkExpr(e, acc)
    | _ => ()
    }
  })
  acc
}

/// Walk an expression to find any nested BlockIfExpr and check it.
and walkExpr = (e: Ast.located<expr>, acc: array<diagnostic>): array<diagnostic> => {
  switch e.node {
  | BlockIfExpr(b) =>
    let d = checkBlockIfExpr(b, e.loc)
    Array.forEach(d, x => {
      let _ = Array.push(acc, x)
    })
    // Recurse into sub-statements and yields
    let _ = walkExpr(b.condition, acc)
    let _ = walkExpr(b.thenYield, acc)
    let _ = walkExpr(b.elseYield, acc)
  | BinOp(l, _, r) =>
    let _ = walkExpr(l, acc)
    let _ = walkExpr(r, acc)
  | UnaryOp(_, inner) =>
    let _ = walkExpr(inner, acc)
  | ParenExpr(inner) =>
    let _ = walkExpr(inner, acc)
  | CallExpr(_, args) =>
    Array.forEach(args, a => {
      let _ = walkExpr(a, acc)
    })
  | IsNullExpr(inner) =>
    let _ = walkExpr(inner, acc)
  | TypeofExpr(inner) =>
    let _ = walkExpr(inner, acc)
  | CastExpr(_, inner) =>
    let _ = walkExpr(inner, acc)
  | _ => ()
  }
  acc
}

/// Run all v1.1 + v1.2 (L13) + v1.3 (L14) + v1.4 (L15) + v1.5 (L16) well-formedness
/// checks across the module. Returns the accumulated diagnostics; empty
/// array means the module passes.
///
/// Isolated modules (L13) are walked recursively: v1.1 checks continue to
/// apply to the declarations INSIDE an isolated module's body (const decls,
/// region striation, match exhaustiveness, block-if yield shapes), and the
/// L13/L14/L15/L16-specific checks run in addition.
///
/// v1.4 / L15 scoping: the `enclosingCaps` parameter carries the capability
/// set visible at this point. At the top level it is the top-level
/// module's declared capability set; inside an isolated module's body it is
/// that isolated module's declared capability set (disjoint from the
/// top-level set — capabilities do not cross the isolation boundary).
let rec checkDeclaration = (
  m: module_,
  enclosingCaps: array<string>,
  scopeLabel: string,
  decl: Ast.located<declaration>,
  diags: array<diagnostic>,
): unit => {
  switch decl.node {
  | ConstDecl(c) =>
    let d = checkConstDecl(c, decl.loc)
    Array.forEach(d, x => {
      let _ = Array.push(diags, x)
    })
  | RegionDecl(r) =>
    let d = checkStriatedRegion(r, decl.loc)
    Array.forEach(d, x => {
      let _ = Array.push(diags, x)
    })
  | FunctionDecl(fd) =>
    let ctx = buildFunctionContext(fd)
    let _ = walkStatements(ctx, m, fd.body, diags)
    // v1.4 / L15-B: check the function's caps set is scoped to the
    // enclosing module's declared capability set.
    let capDiags = checkFunctionCapsScoped(fd, enclosingCaps, scopeLabel, decl.loc)
    Array.forEach(capDiags, x => {
      let _ = Array.push(diags, x)
    })
  | ModuleIsolatedDecl(im) =>
    // v1.2 / L13: run L13-specific checks on THIS module, then recurse into
    // its body so v1.1 + v1.3 + v1.4 checks fire for nested decls.
    let d = checkIsolatedModule(im, decl.loc)
    Array.forEach(d, x => {
      let _ = Array.push(diags, x)
    })
    // v1.4 / L15-A: collect the isolated module's own capability set and
    // flag duplicates. This set is the scope for L15-B of any functions
    // declared inside this module's body — it does NOT include the
    // top-level capability set.
    let (innerCaps, capDiags) = collectCapabilitiesInScope(
      im.declarations,
      "isolated module '" ++ im.name ++ "'",
    )
    Array.forEach(capDiags, x => {
      let _ = Array.push(diags, x)
    })
    let innerScopeLabel = "isolated module '" ++ im.name ++ "'"
    Array.forEach(im.declarations, nested => {
      checkDeclaration(m, innerCaps, innerScopeLabel, nested, diags)
    })
  | SessionDecl(s) =>
    // v1.3 / L14
    let d = checkSession(s, m, decl.loc)
    Array.forEach(d, x => {
      let _ = Array.push(diags, x)
    })
  | ChoreographyDecl(c) =>
    // v1.5 / L16
    let d = checkChoreography(c, m, decl.loc)
    Array.forEach(d, x => {
      let _ = Array.push(diags, x)
    })
  | _ => ()
  }
}

let checkModule = (m: module_): array<diagnostic> => {
  let diags: array<diagnostic> = []
  // v1.4 / L15-A (top level): collect the top-level capability set and
  // flag duplicates. This set is the scope for L15-B of any function
  // declared at the top level (i.e. NOT inside an isolated module).
  let (topCaps, topCapDiags) = collectCapabilitiesInScope(
    m.declarations,
    "top-level module",
  )
  Array.forEach(topCapDiags, x => {
    let _ = Array.push(diags, x)
  })
  Array.forEach(m.declarations, decl => {
    checkDeclaration(m, topCaps, "top-level module", decl, diags)
  })
  diags
}

/// Convenience: true iff `checkModule(m)` produced no diagnostics.
let moduleIsValid = (m: module_): bool => {
  Array.length(checkModule(m)) == 0
}
