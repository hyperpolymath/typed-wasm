// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Parser.res — Recursive descent parser for typed-wasm (.twasm) syntax.
//
// Parses a stream of tokens (from Lexer.res) into an AST (from Ast.res).
// The parser implements the grammar defined in spec/grammar.ebnf.
//
// This is Level 1 of the typed-wasm type safety stack: parse-time validity.
// A successful parse proves that the program is syntactically well-formed.
//
// Error reporting includes source location (line:col) and expected/found
// token information.
//
// panic-attack classification notes:
//
//   allocations (6 hits): All array allocations in this file are normal
//   parser-ast-construction — building field lists, statement lists, variant
//   lists, initialiser lists, etc.  These are bounded by source-text size and
//   are the expected output of a recursive-descent parser.  No unbounded or
//   leaking allocations exist.  Classification: parser-ast-allocation.
//
//   unsafe_blocks (Array.setUnsafe, 2 hits): See the comment on expectRAngle
//   below.  Both are guarded-token-stream-mutations.  Classification:
//   guarded-token-stream-mutation.

open Lexer
open Ast

/// Parse error with location.
type parseError = {
  message: string,
  loc: Lexer.loc,
}

/// Parser result type.
type result<'a> = Result.t<'a, parseError>

/// Parser state: a token stream with a cursor.
type parserState = {
  tokens: array<Lexer.located<Lexer.token>>,
  mutable pos: int,
}

/// Create a parser from source text.
let make = (source: string): parserState => {
  tokens: Lexer.tokenize(source),
  pos: 0,
}

// ============================================================================
// Parser Utilities
// ============================================================================

/// Get the current token.
let current = (p: parserState): Lexer.located<Lexer.token> => {
  if p.pos < Array.length(p.tokens) {
    p.tokens[p.pos]->Option.getOr({Lexer.value: EOF, loc: {line: 0, col: 0}})
  } else {
    {value: EOF, loc: {line: 0, col: 0}}
  }
}

/// Peek at the current token value.
let peek = (p: parserState): Lexer.token => {
  current(p).value
}

/// Get current location.
let loc = (p: parserState): Lexer.loc => {
  current(p).loc
}

/// Advance to the next token.
let advance = (p: parserState): unit => {
  if p.pos < Array.length(p.tokens) {
    p.pos = p.pos + 1
  }
}

/// Expect a specific token. Returns Ok(()) if found, Error if not.
let expect = (p: parserState, expected: Lexer.token): result<unit> => {
  if peek(p) == expected {
    advance(p)
    Ok()
  } else {
    Error({message: `Expected token, found something else`, loc: loc(p)})
  }
}

/// Convert context-sensitive keywords to their string representation.
/// These keywords can also appear as identifiers (field names, region names, etc.)
/// when the parser expects an identifier in a non-keyword position.
let keywordToIdent = (tok: Lexer.token): option<string> => {
  switch tok {
  | Ident(name) => Some(name)
  // Context-sensitive keywords that may appear as field names
  | Initial => Some("initial")
  | Maximum => Some("maximum")
  | Shared => Some("shared")
  | Align => Some("align")
  | Place => Some("place")
  | At => Some("at")
  | From => Some("from")
  | Across => Some("across")
  | Holds => Some("holds")
  | Proof => Some("proof")
  | Lifetime => Some("lifetime")
  | Union => Some("union")
  | Void => Some("void")
  // Effects can also be identifiers in some contexts
  | EffRead => Some("Read")
  | EffWrite => Some("Write")
  | EffAlloc => Some("Alloc")
  | EffFree => Some("Free")
  | EffReadRegion => Some("ReadRegion")
  | EffWriteRegion => Some("WriteRegion")
  | _ => None
  }
}

/// Expect an identifier. Returns the name.
/// Also accepts context-sensitive keywords as identifiers.
let expectIdent = (p: parserState): result<string> => {
  switch keywordToIdent(peek(p)) {
  | Some(name) =>
    advance(p)
    Ok(name)
  | None => Error({message: "Expected identifier", loc: loc(p)})
  }
}

/// Expect a closing angle bracket (>). Handles the >> token that the lexer
/// produces for nested generics like opt<ptr<T>> by splitting it into > and
/// replacing the current token with the remaining >.
///
/// panic-attack classification: the two Array.setUnsafe calls below are
/// guarded-token-stream-mutations.  Both execute only inside a branch where
/// the current token is known to be at a valid index (we only get here after
/// a successful peek which checks bounds).  The mutation replaces the current
/// token with a synthesised remainder token to split a two-char lexeme (>>
/// or >=) into its components.  No out-of-bounds write is possible.
let expectRAngle = (p: parserState): result<unit> => {
  switch peek(p) {
  | RAngle =>
    advance(p)
    Ok()
  | RShift =>
    // >> was lexed as a single token; consume it and inject a > back
    // by replacing the current token in the token array
    let currentToken = current(p)
    let _ = Array.setUnsafe(
      p.tokens,
      p.pos,
      {Lexer.value: RAngle, loc: {line: currentToken.loc.line, col: currentToken.loc.col + 1}},
    )
    Ok()
  | GtEq =>
    // >= was lexed as a single token; split into > and =
    let currentToken = current(p)
    let _ = Array.setUnsafe(
      p.tokens,
      p.pos,
      {Lexer.value: Eq, loc: {line: currentToken.loc.line, col: currentToken.loc.col + 1}},
    )
    Ok()
  | _ => Error({message: "Expected >", loc: loc(p)})
  }
}

/// Expect an integer literal.
let expectInt = (p: parserState): result<int> => {
  switch peek(p) {
  | IntLiteral(n) =>
    advance(p)
    Ok(n)
  | _ => Error({message: "Expected integer literal", loc: loc(p)})
  }
}

/// Expect a string literal.
let expectString = (p: parserState): result<string> => {
  switch peek(p) {
  | StringLiteral(s) =>
    advance(p)
    Ok(s)
  | _ => Error({message: "Expected string literal", loc: loc(p)})
  }
}

/// Helper: wrap a value with the current location.
let located = (p: parserState, node: 'a): Ast.located<'a> => {
  {node, loc: loc(p)}
}

// ============================================================================
// Type Parsing
// ============================================================================

/// Parse a primitive type.
let parsePrimitiveType = (p: parserState): result<Ast.primitiveType> => {
  let typ = switch peek(p) {
  | TyI8 => Some(I8)
  | TyI16 => Some(I16)
  | TyI32 => Some(I32)
  | TyI64 => Some(I64)
  | TyU8 => Some(U8)
  | TyU16 => Some(U16)
  | TyU32 => Some(U32)
  | TyU64 => Some(U64)
  | TyF32 => Some(F32)
  | TyF64 => Some(F64)
  | TyBool => Some(Bool)
  | _ => None
  }
  switch typ {
  | Some(t) =>
    advance(p)
    Ok(t)
  | None => Error({message: "Expected primitive type", loc: loc(p)})
  }
}

/// Parse a field type (recursive).
let rec parseFieldType = (p: parserState): result<Ast.located<Ast.fieldType>> => {
  let startLoc = loc(p)

  switch peek(p) {
  // Pointer types: ptr<T>, ref<T>, unique<T>
  | Ptr =>
    advance(p)
    let _ = expect(p, LAngle)
    switch parseFieldType(p) {
    | Ok(inner) =>
      switch expectRAngle(p) {
      | Ok() => Ok({node: PointerType(PtrOwning, inner), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Ref =>
    advance(p)
    let _ = expect(p, LAngle)
    switch parseFieldType(p) {
    | Ok(inner) =>
      switch expectRAngle(p) {
      | Ok() => Ok({node: PointerType(RefBorrow, inner), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Unique =>
    advance(p)
    let _ = expect(p, LAngle)
    switch parseFieldType(p) {
    | Ok(inner) =>
      switch expectRAngle(p) {
      | Ok() => Ok({node: PointerType(UniqueExcl, inner), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  // Optional: opt<T>
  | Opt =>
    advance(p)
    let _ = expect(p, LAngle)
    switch parseFieldType(p) {
    | Ok(inner) =>
      switch expectRAngle(p) {
      | Ok() => Ok({node: OptionalType(inner), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  // Region reference: @RegionName
  | At =>
    advance(p)
    switch expectIdent(p) {
    | Ok(name) => Ok({node: RegionRef(name), loc: startLoc})
    | Error(e) => Error(e)
    }
  // Union: union { tag: type; ... }
  | Union =>
    advance(p)
    let _ = expect(p, LBrace)
    let variants = []
    let rec parseVariants = () => {
      if peek(p) != RBrace {
        switch expectIdent(p) {
        | Ok(tag) =>
          switch expect(p, Colon) {
          | Ok() =>
            switch parseFieldType(p) {
            | Ok(vType) =>
              let _ = expect(p, Semicolon)
              let _ = Array.push(variants, {node: {tag, variantType: vType}, loc: startLoc})
              parseVariants()
            | Error(e) => Error(e)
            }
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      } else {
        Ok()
      }
    }
    switch parseVariants() {
    | Ok() =>
      switch expect(p, RBrace) {
      | Ok() => Ok({node: UnionType(variants), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  // Primitive types, then check for array suffix [N]
  | _ =>
    switch parsePrimitiveType(p) {
    | Ok(prim) =>
      // Check for array suffix: type[N]
      if peek(p) == LBracket {
        advance(p)
        switch parseExpr(p) {
        | Ok(sizeExpr) =>
          switch expect(p, RBracket) {
          | Ok() =>
            Ok({
              node: ArrayFieldType({node: Primitive(prim), loc: startLoc}, sizeExpr),
              loc: startLoc,
            })
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      } else {
        Ok({node: Primitive(prim), loc: startLoc})
      }
    | Error(_) =>
      // If not a primitive, try identifier as a region reference (e.g. ptr<FreeSlot>)
      switch keywordToIdent(peek(p)) {
      | Some(name) =>
        advance(p)

        // Check for array suffix: RegionName[N]
        if peek(p) == LBracket {
          advance(p)
          switch parseExpr(p) {
          | Ok(sizeExpr) =>
            switch expect(p, RBracket) {
            | Ok() =>
              Ok({
                node: ArrayFieldType({node: RegionRef(name), loc: startLoc}, sizeExpr),
                loc: startLoc,
              })
            | Error(e) => Error(e)
            }
          | Error(e) => Error(e)
          }
        } else {
          Ok({node: RegionRef(name), loc: startLoc})
        }
      | None => Error({message: "Expected field type", loc: startLoc})
      }
    }
  }
}

// ============================================================================
// Expression Parsing (Pratt parser / precedence climbing)
// ============================================================================

/// Parse a primary expression (atoms).
and parsePrimary = (p: parserState): result<Ast.located<Ast.expr>> => {
  let startLoc = loc(p)

  switch peek(p) {
  | IntLiteral(n) =>
    advance(p)
    Ok({node: IntLit(n), loc: startLoc})
  | FloatLiteral(f) =>
    advance(p)
    Ok({node: FloatLit(f), loc: startLoc})
  | StringLiteral(s) =>
    advance(p)
    Ok({node: StringLit(s), loc: startLoc})
  | True =>
    advance(p)
    Ok({node: BoolLit(true), loc: startLoc})
  | False =>
    advance(p)
    Ok({node: BoolLit(false), loc: startLoc})
  | Null =>
    advance(p)
    Ok({node: NullLit, loc: startLoc})
  | Dollar =>
    advance(p)
    switch expectIdent(p) {
    | Ok(name) => Ok({node: RegionVar(name), loc: startLoc})
    | Error(e) => Error(e)
    }
  | Sizeof =>
    advance(p)
    let _ = expect(p, LParen)
    switch expectIdent(p) {
    | Ok(name) =>
      switch expect(p, RParen) {
      | Ok() => Ok({node: SizeofExpr(name), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | IsNull =>
    advance(p)
    let _ = expect(p, LParen)
    switch parseExpr(p) {
    | Ok(inner) =>
      switch expect(p, RParen) {
      | Ok() => Ok({node: IsNullExpr(inner), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | IsValid =>
    advance(p)
    let _ = expect(p, LParen)
    let _ = expect(p, Dollar)
    switch expectIdent(p) {
    | Ok(name) =>
      switch expect(p, RParen) {
      | Ok() => Ok({node: IsValidExpr(name), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Cast =>
    advance(p)
    let _ = expect(p, LAngle)
    switch parseFieldType(p) {
    | Ok(ty) =>
      let _ = expectRAngle(p)
      let _ = expect(p, LParen)
      switch parseExpr(p) {
      | Ok(inner) =>
        switch expect(p, RParen) {
        | Ok() => Ok({node: CastExpr(ty, inner), loc: startLoc})
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | LParen =>
    advance(p)
    switch parseExpr(p) {
    | Ok(inner) =>
      switch expect(p, RParen) {
      | Ok() => Ok({node: ParenExpr(inner), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  // Unary operators
  | Minus =>
    advance(p)
    switch parsePrimary(p) {
    | Ok(inner) => Ok({node: UnaryOp(Neg, inner), loc: startLoc})
    | Error(e) => Error(e)
    }
  | Bang =>
    advance(p)
    switch parsePrimary(p) {
    | Ok(inner) => Ok({node: UnaryOp(Not, inner), loc: startLoc})
    | Error(e) => Error(e)
    }
  // Borrow expressions: &expr, &mut expr
  // These are passed through as the inner expression — borrow semantics
  // are enforced by the type checker, not the parser.
  | Ampersand =>
    advance(p)
    switch parsePrimary(p) {
    | Ok(inner) => Ok(inner) // Pass through — borrow is semantic
    | Error(e) => Error(e)
    }
  | AmpMut =>
    advance(p)
    switch parsePrimary(p) {
    | Ok(inner) => Ok(inner) // Pass through — mutable borrow is semantic
    | Error(e) => Error(e)
    }
  | Tilde =>
    advance(p)
    switch parsePrimary(p) {
    | Ok(inner) => Ok({node: UnaryOp(BitNot, inner), loc: startLoc})
    | Error(e) => Error(e)
    }
  // Identifier (possibly a function call)
  | Ident(name) =>
    advance(p)
    if peek(p) == LParen {
      advance(p)
      let args = []
      let rec parseArgs = () => {
        if peek(p) != RParen {
          switch parseExpr(p) {
          | Ok(arg) =>
            let _ = Array.push(args, arg)
            if peek(p) == Comma {
              advance(p)
            }
            parseArgs()
          | Error(e) => Error(e)
          }
        } else {
          Ok()
        }
      }
      switch parseArgs() {
      | Ok() =>
        switch expect(p, RParen) {
        | Ok() => Ok({node: CallExpr(name, args), loc: startLoc})
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    } else {
      Ok({node: Identifier(name), loc: startLoc})
    }

  // v1.1: block-expression `if cond { stmts; yield e } else { stmts; yield e }`
  //
  // Distinct from the statement-form `if` handled in parseStatement: this
  // form is reachable only from expression position (e.g. `let x = if ...`)
  // and REQUIRES a `yield` expression as the last statement of each branch.
  // parseStatement intercepts `if` at the statement level and produces an
  // IfStmt, so this branch only fires when parsePrimary is called from
  // parseExpr in a non-statement context.
  //
  // Both `yield` expressions must have the same type (checked by
  // Checker.blockIfBranchesAgree).
  | If =>
    advance(p) // consume 'if'
    switch parseExpr(p) {
    | Error(e) => Error(e)
    | Ok(condition) =>
      switch expect(p, LBrace) {
      | Error(e) => Error(e)
      | Ok() =>
        // Parse zero-or-more statements, then a terminating `yield expr`.
        let thenStmts: array<Ast.located<Ast.statement>> = []
        let rec parseThenStmts = () => {
          switch peek(p) {
          | Yield => Ok()
          | RBrace => Error({message: "Block-if then-branch must end with `yield`", loc: loc(p)})
          | _ =>
            switch parseStatement(p) {
            | Error(e) => Error(e)
            | Ok(s) =>
              let _ = Array.push(thenStmts, s)
              parseThenStmts()
            }
          }
        }
        switch parseThenStmts() {
        | Error(e) => Error(e)
        | Ok() =>
          advance(p) // consume 'yield'
          switch parseExpr(p) {
          | Error(e) => Error(e)
          | Ok(thenYield) =>
            // Optional trailing semicolon after the yield expression.
            if peek(p) == Semicolon {
              advance(p)
            }
            switch expect(p, RBrace) {
            | Error(e) => Error(e)
            | Ok() =>
              switch expect(p, Else) {
              | Error(e) => Error(e)
              | Ok() =>
                switch expect(p, LBrace) {
                | Error(e) => Error(e)
                | Ok() =>
                  let elseStmts: array<Ast.located<Ast.statement>> = []
                  let rec parseElseStmts = () => {
                    switch peek(p) {
                    | Yield => Ok()
                    | RBrace =>
                      Error({
                        message: "Block-if else-branch must end with `yield`",
                        loc: loc(p),
                      })
                    | _ =>
                      switch parseStatement(p) {
                      | Error(e) => Error(e)
                      | Ok(s) =>
                        let _ = Array.push(elseStmts, s)
                        parseElseStmts()
                      }
                    }
                  }
                  switch parseElseStmts() {
                  | Error(e) => Error(e)
                  | Ok() =>
                    advance(p) // consume 'yield'
                    switch parseExpr(p) {
                    | Error(e) => Error(e)
                    | Ok(elseYield) =>
                      if peek(p) == Semicolon {
                        advance(p)
                      }
                      switch expect(p, RBrace) {
                      | Error(e) => Error(e)
                      | Ok() =>
                        Ok({
                          node: BlockIfExpr({
                            condition,
                            thenStmts,
                            thenYield,
                            elseStmts,
                            elseYield,
                          }),
                          loc: startLoc,
                        })
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

  | _ => Error({message: "Expected expression", loc: startLoc})
  }
}

/// Get the precedence of a binary operator token.
and binOpPrecedence = (tok: Lexer.token): option<(Ast.binOp, int)> => {
  switch tok {
  | PipePipe => Some((Or, 1))
  | AmpAmp => Some((And, 2))
  | Pipe => Some((BitOr, 3))
  | Caret => Some((BitXor, 4))
  | Ampersand => Some((BitAnd, 5))
  | EqEq => Some((Eq, 6))
  | BangEq => Some((NotEq, 6))
  | LAngle => Some((Lt, 7))
  | RAngle => Some((Gt, 7))
  | LtEq => Some((LtEq, 7))
  | GtEq => Some((GtEq, 7))
  | LShift => Some((Shl, 8))
  | RShift => Some((Shr, 8))
  | Plus => Some((Add, 9))
  | Minus => Some((Sub, 9))
  | Star => Some((Mul, 10))
  | Slash => Some((Div, 10))
  | Percent => Some((Mod, 10))
  | _ => None
  }
}

/// Parse an expression with precedence climbing.
and parseExprPrec = (p: parserState, minPrec: int): result<Ast.located<Ast.expr>> => {
  switch parsePrimary(p) {
  | Ok(left) =>
    let rec loop = left => {
      switch binOpPrecedence(peek(p)) {
      | Some((op, prec)) if prec >= minPrec =>
        advance(p)
        switch parseExprPrec(p, prec + 1) {
        | Ok(right) =>
          let combined = {node: BinOp(left, op, right), loc: left.loc}
          loop(combined)
        | Error(e) => Error(e)
        }
      | _ => Ok(left)
      }
    }
    loop(left)
  | Error(e) => Error(e)
  }
}

/// Parse a full expression.
and parseExpr = (p: parserState): result<Ast.located<Ast.expr>> => {
  parseExprPrec(p, 0)
}

// ============================================================================
// Statement Parsing
// ============================================================================

/// Parse a region target: $name or $name[index]
and parseRegionTarget = (p: parserState): result<Ast.regionTarget> => {
  let _ = expect(p, Dollar)
  switch expectIdent(p) {
  | Ok(name) =>
    if peek(p) == LBracket {
      advance(p)
      switch parseExpr(p) {
      | Ok(idx) =>
        switch expect(p, RBracket) {
        | Ok() => Ok({name, index: Some(idx)})
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    } else {
      Ok({name, index: None})
    }
  | Error(e) => Error(e)
  }
}

/// Parse a field path: .field.subfield[index]...
and parseFieldPath = (p: parserState): result<array<Ast.fieldPathSegment>> => {
  let segments = []
  let rec loop = () => {
    switch peek(p) {
    | Dot =>
      advance(p)
      switch expectIdent(p) {
      | Ok(name) =>
        let _ = Array.push(segments, FieldAccess(name))
        loop()
      | Error(e) => Error(e)
      }
    | LBracket =>
      advance(p)
      switch parseExpr(p) {
      | Ok(idx) =>
        switch expect(p, RBracket) {
        | Ok() =>
          let _ = Array.push(segments, IndexAccess(idx))
          loop()
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | _ => Ok(segments)
    }
  }
  loop()
}

/// Parse a single statement.
// NOTE: parseStatement and parseBlock are intentionally in the SAME
// mutually-recursive group as parsePrimary / parseExpr above. This is
// required for v1.1 block-expression `if`: parsePrimary's BlockIfExpr
// branch calls parseStatement to parse statements inside the block
// before the final `yield`. Without the merge, parsePrimary cannot reach
// parseStatement because it is defined later in the file.
and parseStatement = (p: parserState): result<Ast.located<Ast.statement>> => {
  let startLoc = loc(p)

  switch peek(p) {
  // region.get $target .path -> binding
  | RegionGet =>
    advance(p)
    switch parseRegionTarget(p) {
    | Ok(target) =>
      switch parseFieldPath(p) {
      | Ok(path) =>
        let binding = if peek(p) == Arrow {
          advance(p)
          switch expectIdent(p) {
          | Ok(name) => Some(name)
          | Error(_) => None
          }
        } else {
          None
        }
        let _ = expect(p, Semicolon)
        Ok({node: RegionGetStmt({target, fieldPath: path, binding}), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // region.set $target .path, value
  | RegionSet =>
    advance(p)
    switch parseRegionTarget(p) {
    | Ok(target) =>
      switch parseFieldPath(p) {
      | Ok(path) =>
        switch expect(p, Comma) {
        | Ok() =>
          switch parseExpr(p) {
          | Ok(value) =>
            let _ = expect(p, Semicolon)
            Ok({node: RegionSetStmt({target, fieldPath: path, value}), loc: startLoc})
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // region.scan $target where pred -> |binding| { body }
  | RegionScan =>
    advance(p)
    switch parseRegionTarget(p) {
    | Ok(target) =>
      // Optional where predicate
      let predicate = if peek(p) == Where {
        advance(p)
        switch parseExpr(p) {
        | Ok(pred) => Some(pred)
        | Error(_) => None
        }
      } else {
        None
      }
      // Optional -> |binding| { body }
      let bindingName = if peek(p) == Arrow {
        advance(p)
        if peek(p) == Pipe {
          advance(p) // consume |
          switch expectIdent(p) {
          | Ok(name) =>
            let _ = expect(p, Pipe) // closing |
            Some(name)
          | Error(_) => None
          }
        } else {
          None
        }
      } else {
        None
      }
      switch expect(p, LBrace) {
      | Ok() =>
        switch parseBlock(p) {
        | Ok(body) =>
          switch expect(p, RBrace) {
          | Ok() =>
            Ok({node: RegionScanStmt({target, predicate, bindingName, body}), loc: startLoc})
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // region.alloc RegionName { inits } -> binding
  | RegionAlloc =>
    advance(p)
    switch expectIdent(p) {
    | Ok(regionName) =>
      let inits = []
      if peek(p) == LBrace {
        advance(p)
        let rec parseInits = () => {
          if peek(p) != RBrace {
            switch expectIdent(p) {
            | Ok(fieldName) =>
              switch expect(p, Eq) {
              | Ok() =>
                switch parseExpr(p) {
                | Ok(value) =>
                  let _ = Array.push(inits, (fieldName, value))
                  if peek(p) == Comma {
                    advance(p)
                  }
                  parseInits()
                | Error(e) => Error(e)
                }
              | Error(e) => Error(e)
              }
            | Error(e) => Error(e)
            }
          } else {
            Ok()
          }
        }
        switch parseInits() {
        | Ok() =>
          let _ = expect(p, RBrace)
        | Error(e) => ignore(Error(e))
        }
      }
      switch expect(p, Arrow) {
      | Ok() =>
        switch expectIdent(p) {
        | Ok(binding) =>
          let _ = expect(p, Semicolon)
          Ok({node: RegionAllocStmt({regionName, initializers: inits, binding}), loc: startLoc})
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // region.free $name
  | RegionFree =>
    advance(p)
    let _ = expect(p, Dollar)
    switch expectIdent(p) {
    | Ok(name) =>
      let _ = expect(p, Semicolon)
      Ok({node: RegionFreeStmt(name), loc: startLoc})
    | Error(e) => Error(e)
    }

  // let [mut] name [: type] = expr;
  | Let =>
    advance(p)
    let isMut = peek(p) == Mut
    if isMut {
      advance(p)
    }
    switch expectIdent(p) {
    | Ok(name) =>
      let typeAnn = if peek(p) == Colon {
        advance(p)
        let tyLoc = loc(p)
        // Handle region handle types: own region<X>, &region<X>, &mut region<X>
        switch peek(p) {
        | Own =>
          advance(p)
          let _ = expect(p, Region)
          let _ = expect(p, LAngle)
          switch expectIdent(p) {
          | Ok(regionName) =>
            let _ = expectRAngle(p)
            Some(({node: RegionRef(regionName), loc: tyLoc}: Ast.located<Ast.fieldType>))
          | Error(_) => None
          }
        | Ampersand =>
          let saved = p.pos
          advance(p)
          if peek(p) == Region {
            let _ = expect(p, Region)
            let _ = expect(p, LAngle)
            switch expectIdent(p) {
            | Ok(regionName) =>
              let _ = expectRAngle(p)
              Some(({node: RegionRef(regionName), loc: tyLoc}: Ast.located<Ast.fieldType>))
            | Error(_) => None
            }
          } else {
            p.pos = saved
            switch parseFieldType(p) {
            | Ok(ty) => Some(ty)
            | Error(_) => None
            }
          }
        | AmpMut =>
          let saved = p.pos
          advance(p)
          if peek(p) == Region {
            let _ = expect(p, Region)
            let _ = expect(p, LAngle)
            switch expectIdent(p) {
            | Ok(regionName) =>
              let _ = expectRAngle(p)
              Some(({node: RegionRef(regionName), loc: tyLoc}: Ast.located<Ast.fieldType>))
            | Error(_) => None
            }
          } else {
            p.pos = saved
            switch parseFieldType(p) {
            | Ok(ty) => Some(ty)
            | Error(_) => None
            }
          }
        | _ =>
          switch parseFieldType(p) {
          | Ok(ty) => Some(ty)
          | Error(_) => None
          }
        }
      } else {
        None
      }
      switch expect(p, Eq) {
      | Ok() =>
        switch parseExpr(p) {
        | Ok(init) =>
          let _ = expect(p, Semicolon)
          Ok({
            node: LetStmt({isMutable: isMut, name, typeAnnotation: typeAnn, initializer: init}),
            loc: startLoc,
          })
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // if expr { stmts } [else { stmts }]
  | If =>
    advance(p)
    switch parseExpr(p) {
    | Ok(cond) =>
      switch expect(p, LBrace) {
      | Ok() =>
        switch parseBlock(p) {
        | Ok(thenBody) =>
          switch expect(p, RBrace) {
          | Ok() =>
            let elseBody = if peek(p) == Else {
              advance(p)
              let _ = expect(p, LBrace)
              switch parseBlock(p) {
              | Ok(body) =>
                let _ = expect(p, RBrace)
                Some(body)
              | Error(_) => None
              }
            } else {
              None
            }
            Ok({
              node: IfStmt({condition: cond, thenBranch: thenBody, elseBranch: elseBody}),
              loc: startLoc,
            })
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // while expr { stmts }
  | While =>
    advance(p)
    switch parseExpr(p) {
    | Ok(cond) =>
      switch expect(p, LBrace) {
      | Ok() =>
        switch parseBlock(p) {
        | Ok(body) =>
          switch expect(p, RBrace) {
          | Ok() => Ok({node: WhileStmt({condition: cond, body}), loc: startLoc})
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // return [expr];
  | Return =>
    advance(p)
    if peek(p) == Semicolon {
      advance(p)
      Ok({node: ReturnStmt(None), loc: startLoc})
    } else {
      switch parseExpr(p) {
      | Ok(value) =>
        let _ = expect(p, Semicolon)
        Ok({node: ReturnStmt(Some(value)), loc: startLoc})
      | Error(e) => Error(e)
      }
    }

  // static_assert proposition;
  | StaticAssert =>
    advance(p)
    switch parseExpr(p) {
    | Ok(prop) =>
      let _ = expect(p, Semicolon)
      Ok({node: StaticAssertStmt(prop), loc: startLoc})
    | Error(e) => Error(e)
    }

  // proof name { given: ...; show: ...; by: ...; }
  | Proof =>
    advance(p)
    switch expectIdent(p) {
    | Ok(name) =>
      let _ = expect(p, LBrace)
      let steps: array<Ast.located<Ast.proofStep>> = []
      let rec parseProofBody = () => {
        switch peek(p) {
        | RBrace => Ok()
        | Given =>
          advance(p)
          let _ = expect(p, Colon)
          // Parse the given expression — may contain complex syntax
          // so we skip to semicolon for robustness
          let proofStepLoc = loc(p)
          switch parseExpr(p) {
          | Ok(expr) =>
            let _ = expect(p, Semicolon)
            let _ = Array.push(steps, {node: GivenStep(expr), loc: proofStepLoc})
            parseProofBody()
          | Error(_) =>
            // Skip to semicolon on parse failure (proof expressions may use
            // syntax like forall/=> that the expression parser doesn't handle)
            while peek(p) != Semicolon && peek(p) != RBrace && peek(p) != EOF {
              advance(p)
            }
            let _ = expect(p, Semicolon)
            parseProofBody()
          }
        | Show =>
          advance(p)
          let _ = expect(p, Colon)
          let proofStepLoc = loc(p)
          switch parseExpr(p) {
          | Ok(expr) =>
            let _ = expect(p, Semicolon)
            let _ = Array.push(steps, {node: ShowStep(expr), loc: proofStepLoc})
            parseProofBody()
          | Error(_) =>
            // Skip complex proof expressions
            while peek(p) != Semicolon && peek(p) != RBrace && peek(p) != EOF {
              advance(p)
            }
            let _ = expect(p, Semicolon)
            parseProofBody()
          }
        | By =>
          advance(p)
          let _ = expect(p, Colon)
          let proofStepLoc = loc(p)
          let tactic = switch peek(p) {
          | TacticBoundsCheck =>
            advance(p)
            BoundsCheck
          | TacticLinearity =>
            advance(p)
            Linearity
          | TacticLifetime =>
            advance(p)
            Lifetime
          | TacticAliasFreedom =>
            advance(p)
            AliasFreedom
          | TacticEffectPurity =>
            advance(p)
            EffectPurity
          | TacticInduction =>
            advance(p)
            let _ = expect(p, LParen)
            let name = switch expectIdent(p) {
            | Ok(n) => n
            | Error(_) => "unknown"
            }
            let _ = expect(p, RParen)
            Induction(name)
          | TacticRewrite =>
            advance(p)
            let _ = expect(p, LParen)
            let name = switch expectIdent(p) {
            | Ok(n) => n
            | Error(_) => "unknown"
            }
            let _ = expect(p, RParen)
            Rewrite(name)
          | _ =>
            // Skip unknown tactics
            while peek(p) != Semicolon && peek(p) != RBrace && peek(p) != EOF {
              advance(p)
            }
            BoundsCheck
          }
          let _ = expect(p, Semicolon)
          let _ = Array.push(steps, {node: ByStep(tactic), loc: proofStepLoc})
          parseProofBody()
        | _ =>
          // Skip unknown proof content
          advance(p)
          parseProofBody()
        }
      }
      switch parseProofBody() {
      | Ok() =>
        let _ = expect(p, RBrace)
        Ok({node: ProofStmt({name, steps}), loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }

  // v1.1: match $target .field { | Tag => { body } | ... }
  | Match =>
    advance(p) // consume 'match'
    switch parseRegionTarget(p) {
    | Error(e) => Error(e)
    | Ok(target) =>
      switch parseFieldPath(p) {
      | Error(e) => Error(e)
      | Ok(fieldPath) =>
        switch expect(p, LBrace) {
        | Error(e) => Error(e)
        | Ok() =>
          let arms: array<Ast.located<Ast.matchArm>> = []
          let rec parseArms = () => {
            switch peek(p) {
            | RBrace => Ok()
            | Pipe =>
              let armLoc = loc(p)
              advance(p) // consume '|'
              switch expectIdent(p) {
              | Error(e) => Error(e)
              | Ok(tag) =>
                // '=>' is lexed as Eq followed by RAngle — the parser does
                // not have a dedicated FatArrow token yet.
                switch expect(p, Eq) {
                | Error(e) => Error(e)
                | Ok() =>
                  switch expect(p, RAngle) {
                  | Error(e) => Error(e)
                  | Ok() =>
                    switch expect(p, LBrace) {
                    | Error(e) => Error(e)
                    | Ok() =>
                      switch parseBlock(p) {
                      | Error(e) => Error(e)
                      | Ok(body) =>
                        switch expect(p, RBrace) {
                        | Error(e) => Error(e)
                        | Ok() =>
                          let _ = Array.push(
                            arms,
                            {node: ({tag, body}: Ast.matchArm), loc: armLoc},
                          )
                          parseArms()
                        }
                      }
                    }
                  }
                }
              }
            | _ => Error({message: "Expected `|` or `}` in match body", loc: loc(p)})
            }
          }
          switch parseArms() {
          | Error(e) => Error(e)
          | Ok() =>
            switch expect(p, RBrace) {
            | Error(e) => Error(e)
            | Ok() =>
              Ok({node: MatchStmt({target, fieldPath, arms}), loc: startLoc})
            }
          }
        }
      }
    }

  // Default: expression statement or assignment (e.g., count = count + 1;)
  | _ =>
    switch parseExpr(p) {
    | Ok(expr) =>
      // Check for assignment: expr = value;
      if peek(p) == Eq {
        advance(p)
        switch parseExpr(p) {
        | Ok(value) =>
          let _ = expect(p, Semicolon)
          // Encode assignment as a let statement on the same name (mutable reassignment)
          switch expr.node {
          | Identifier(name) =>
            Ok({
              node: LetStmt({isMutable: true, name, typeAnnotation: None, initializer: value}),
              loc: startLoc,
            })
          | _ =>
            // For non-identifier assignments, encode as expression statement
            Ok({node: ExprStmt({node: BinOp(expr, Eq, value), loc: startLoc}), loc: startLoc})
          }
        | Error(e) => Error(e)
        }
      } else {
        let _ = expect(p, Semicolon)
        Ok({node: ExprStmt(expr), loc: startLoc})
      }
    | Error(e) => Error(e)
    }
  }
}

/// Parse a block of statements (until closing brace).
and parseBlock = (p: parserState): result<array<Ast.located<Ast.statement>>> => {
  let stmts = []
  let rec loop = () => {
    if peek(p) != RBrace && peek(p) != EOF {
      switch parseStatement(p) {
      | Ok(stmt) =>
        let _ = Array.push(stmts, stmt)
        loop()
      | Error(e) => Error(e)
      }
    } else {
      Ok(stmts)
    }
  }
  loop()
}

// ============================================================================
// Declaration Parsing
// ============================================================================

/// Parse a field declaration: name: type [where constraints];
let parseFieldDecl = (p: parserState): result<Ast.located<Ast.fieldDecl>> => {
  let startLoc = loc(p)
  switch expectIdent(p) {
  | Ok(name) =>
    switch expect(p, Colon) {
    | Ok() =>
      switch parseFieldType(p) {
      | Ok(ty) =>
        // Parse optional constraints
        let constraints = []
        if peek(p) == Where {
          advance(p)
          // Simple: just parse expression as constraint for now
          switch parseExpr(p) {
          | Ok(expr) =>
            let _ = Array.push(
              constraints,
              {node: PredicateConstraint("constraint", [expr]), loc: startLoc},
            )
          | Error(_) => ()
          }
        }
        let _ = expect(p, Semicolon)
        Ok({node: {name, fieldType: ty, constraints}, loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse a region declaration.
let parseRegionDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'region'

  switch expectIdent(p) {
  | Ok(name) =>
    // Optional instance count: [N]
    let instanceCount = if peek(p) == LBracket {
      advance(p)
      switch parseExpr(p) {
      | Ok(count) =>
        let _ = expect(p, RBracket)
        Some(count)
      | Error(_) => None
      }
    } else {
      None
    }

    // v1.1: optional `striated` layout marker between the instance count
    // and the opening brace. Default is AoS (pre-v1.1 behaviour).
    let layout = ref(Ast.LayoutAoS)
    if peek(p) == Striated {
      advance(p)
      layout := Ast.LayoutStriated
    }

    switch expect(p, LBrace) {
    | Ok() =>
      let fields = []
      let alignment = ref(None)
      let invariants = []

      // Parse fields, align, and invariant blocks
      let rec parseBody = () => {
        switch peek(p) {
        | RBrace => Ok()
        | Align =>
          advance(p)
          switch expectInt(p) {
          | Ok(n) =>
            alignment := Some(n)
            let _ = expect(p, Semicolon)
            parseBody()
          | Error(e) => Error(e)
          }
        | Invariant =>
          advance(p)
          let _ = expect(p, LBrace)
          let rec parseInvariants = () => {
            if peek(p) != RBrace {
              switch expectIdent(p) {
              | Ok(invName) =>
                let _ = expect(p, Colon)
                switch parseExpr(p) {
                | Ok(prop) =>
                  let _ = expect(p, Semicolon)
                  let _ = Array.push(
                    invariants,
                    {node: {name: invName, proposition: prop}, loc: startLoc},
                  )
                  parseInvariants()
                | Error(e) => Error(e)
                }
              | Error(e) => Error(e)
              }
            } else {
              Ok()
            }
          }
          switch parseInvariants() {
          | Ok() =>
            let _ = expect(p, RBrace)
            parseBody()
          | Error(e) => Error(e)
          }
        | Where =>
          // Region-level where constraint — skip for now
          advance(p)
          // Consume until semicolon
          while peek(p) != Semicolon && peek(p) != EOF {
            advance(p)
          }
          let _ = expect(p, Semicolon)
          parseBody()
        | _ =>
          switch parseFieldDecl(p) {
          | Ok(field) =>
            let _ = Array.push(fields, field)
            parseBody()
          | Error(e) => Error(e)
          }
        }
      }

      switch parseBody() {
      | Ok() =>
        switch expect(p, RBrace) {
        | Ok() =>
          Ok({
            node: RegionDecl({
              name,
              instanceCount,
              layout: layout.contents, // v1.1: set by the `striated` keyword check above
              fields,
              alignment: alignment.contents,
              invariants,
            }),
            loc: startLoc,
          })
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse effects clause: effects { Read, Write, ... }
/// Parse a flat list of memory effects, stopping at `}` or the start of a
/// split-form transition (comma followed by `caps:`). Used by both the
/// flat-form clause and the split form's `memory:` sub-clause.
///
/// Caller is responsible for consuming the enclosing braces.
let parseFlatEffectList = (p: parserState): result<array<Ast.located<Ast.effect>>> => {
  let effects = []
  let rec loop = () => {
    if peek(p) == RBrace {
      Ok()
    } else {
      let startLoc = loc(p)
      let eff = switch peek(p) {
      | EffRead =>
        advance(p)
        Ok(ReadEffect)
      | EffWrite =>
        advance(p)
        Ok(WriteEffect)
      | EffAlloc =>
        advance(p)
        Ok(AllocEffect)
      | EffFree =>
        advance(p)
        Ok(FreeEffect)
      | EffReadRegion =>
        advance(p)
        let _ = expect(p, LParen)
        switch expectIdent(p) {
        | Ok(name) =>
          let _ = expect(p, RParen)
          Ok(ReadRegionEffect(name))
        | Error(e) => Error(e)
        }
      | EffWriteRegion =>
        advance(p)
        let _ = expect(p, LParen)
        switch expectIdent(p) {
        | Ok(name) =>
          let _ = expect(p, RParen)
          Ok(WriteRegionEffect(name))
        | Error(e) => Error(e)
        }
      | _ => Error({message: "Expected effect", loc: startLoc})
      }
      switch eff {
      | Error(e) => Error(e)
      | Ok(e) =>
        let _ = Array.push(effects, {node: e, loc: startLoc})
        if peek(p) == Comma {
          advance(p)
        }
        loop()
      }
    }
  }
  switch loop() {
  | Error(e) => Error(e)
  | Ok() => Ok(effects)
  }
}

/// Parse a comma-separated capability identifier list up to `}`.
/// Caller is responsible for consuming the enclosing braces.
let parseCapsList = (p: parserState): result<array<Ast.located<string>>> => {
  let caps: array<Ast.located<string>> = []
  let rec loop = () => {
    if peek(p) == RBrace {
      Ok()
    } else {
      let startLoc = loc(p)
      switch expectIdent(p) {
      | Error(e) => Error(e)
      | Ok(name) =>
        let _ = Array.push(caps, {node: name, loc: startLoc})
        if peek(p) == Comma {
          advance(p)
        }
        loop()
      }
    }
  }
  switch loop() {
  | Error(e) => Error(e)
  | Ok() => Ok(caps)
  }
}

/// v1.1: Parse the effects clause, supporting both flat and split forms.
///
///   Flat  (v1.0): effects { Read, Write, ReadRegion(X) }
///   Split (v1.1): effects { memory: { Read, Write }, caps: { read_file, web_fetch } }
///
/// Returns (memory_effects, capabilities). For the flat form, `caps` is
/// always `None`. For the split form, either sub-clause may be missing
/// (both `memory:` and `caps:` are optional, in any order).
///
/// Disambiguation: after consuming `effects {`, peek at the next token.
///   - `Memory` (i.e. the keyword `memory` followed by `:`) → split form
///   - `Ident("caps")` followed by `:` → split form
///   - Anything else → flat form
let parseEffectsClause = (p: parserState): result<(
  option<array<Ast.located<Ast.effect>>>,
  option<array<Ast.located<string>>>,
)> => {
  advance(p) // consume 'effects'
  switch expect(p, LBrace) {
  | Error(e) => Error(e)
  | Ok() =>
    // Detect split vs flat by peeking.
    let isSplit = switch peek(p) {
    | Memory => true
    | Ident(id) => id == "caps"
    | _ => false
    }
    if isSplit {
      // Split form. Accept `memory:` and `caps:` sub-clauses in any order.
      let memRef: ref<option<array<Ast.located<Ast.effect>>>> = ref(None)
      let capsRef: ref<option<array<Ast.located<string>>>> = ref(None)
      let rec loop = () => {
        switch peek(p) {
        | RBrace => Ok()
        | Memory =>
          advance(p) // consume 'memory'
          switch expect(p, Colon) {
          | Error(e) => Error(e)
          | Ok() =>
            switch expect(p, LBrace) {
            | Error(e) => Error(e)
            | Ok() =>
              switch parseFlatEffectList(p) {
              | Error(e) => Error(e)
              | Ok(effs) =>
                switch expect(p, RBrace) {
                | Error(e) => Error(e)
                | Ok() =>
                  memRef := Some(effs)
                  if peek(p) == Comma {
                    advance(p)
                  }
                  loop()
                }
              }
            }
          }
        | Ident(id) if id == "caps" =>
          advance(p) // consume 'caps'
          switch expect(p, Colon) {
          | Error(e) => Error(e)
          | Ok() =>
            switch expect(p, LBrace) {
            | Error(e) => Error(e)
            | Ok() =>
              switch parseCapsList(p) {
              | Error(e) => Error(e)
              | Ok(c) =>
                switch expect(p, RBrace) {
                | Error(e) => Error(e)
                | Ok() =>
                  capsRef := Some(c)
                  if peek(p) == Comma {
                    advance(p)
                  }
                  loop()
                }
              }
            }
          }
        | _ =>
          Error({
            message: "Expected `memory:` or `caps:` in split effects clause, or `}`",
            loc: loc(p),
          })
        }
      }
      switch loop() {
      | Error(e) => Error(e)
      | Ok() =>
        switch expect(p, RBrace) {
        | Error(e) => Error(e)
        | Ok() => Ok((memRef.contents, capsRef.contents))
        }
      }
    } else {
      // Flat form.
      switch parseFlatEffectList(p) {
      | Error(e) => Error(e)
      | Ok(effs) =>
        switch expect(p, RBrace) {
        | Error(e) => Error(e)
        | Ok() => Ok((Some(effs), None))
        }
      }
    }
  }
}

/// Parse a function declaration.
let parseFunctionDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'fn'

  switch expectIdent(p) {
  | Ok(name) =>
    let _ = expect(p, LParen)
    // Parse parameters
    let params = []
    let rec parseParams = () => {
      if peek(p) != RParen {
        let paramLoc = loc(p)
        switch expectIdent(p) {
        | Ok(paramName) =>
          let _ = expect(p, Colon)
          // Determine param type: field type or region handle
          switch peek(p) {
          | Ampersand | AmpMut | Own =>
            let mode = switch peek(p) {
            | AmpMut =>
              advance(p)
              MutableBorrow
            | Ampersand =>
              advance(p)
              SharedBorrow
            | Own =>
              advance(p)
              Owning
            | _ => SharedBorrow
            }
            let _ = expect(p, Region)
            let _ = expect(p, LAngle)
            switch expectIdent(p) {
            | Ok(regionName) =>
              let _ = expectRAngle(p)
              let _ = Array.push(
                params,
                {
                  node: {
                    name: paramName,
                    paramType: {node: RegionHandleParam(mode, regionName), loc: paramLoc},
                  },
                  loc: paramLoc,
                },
              )
              if peek(p) == Comma {
                advance(p)
              }
              parseParams()
            | Error(e) => Error(e)
            }
          | _ =>
            switch parseFieldType(p) {
            | Ok(ty) =>
              let _ = Array.push(
                params,
                {
                  node: {name: paramName, paramType: {node: FieldParam(ty.node), loc: paramLoc}},
                  loc: paramLoc,
                },
              )
              if peek(p) == Comma {
                advance(p)
              }
              parseParams()
            | Error(e) => Error(e)
            }
          }
        | Error(e) => Error(e)
        }
      } else {
        Ok()
      }
    }

    switch parseParams() {
    | Ok() =>
      let _ = expect(p, RParen)

      // Optional return type — may be a field type or a region handle type
      // (own region<X>, &region<X>, &mut region<X>)
      let returnType = if peek(p) == Arrow {
        advance(p)
        let retLoc = loc(p)
        switch peek(p) {
        // own region<X> — owning handle return
        | Own =>
          advance(p)
          let _ = expect(p, Region)
          let _ = expect(p, LAngle)
          switch expectIdent(p) {
          | Ok(regionName) =>
            let _ = expectRAngle(p)
            Some(({node: RegionRef(regionName), loc: retLoc}: Ast.located<Ast.fieldType>))
          | Error(_) => None
          }
        // &region<X> or &mut region<X> — borrowed handle return
        | Ampersand =>
          advance(p)
          let _ = expect(p, Region)
          let _ = expect(p, LAngle)
          switch expectIdent(p) {
          | Ok(regionName) =>
            let _ = expectRAngle(p)
            Some(({node: RegionRef(regionName), loc: retLoc}: Ast.located<Ast.fieldType>))
          | Error(_) => None
          }
        | AmpMut =>
          advance(p)
          let _ = expect(p, Region)
          let _ = expect(p, LAngle)
          switch expectIdent(p) {
          | Ok(regionName) =>
            let _ = expectRAngle(p)
            Some(({node: RegionRef(regionName), loc: retLoc}: Ast.located<Ast.fieldType>))
          | Error(_) => None
          }
        // Regular field type
        | _ =>
          switch parseFieldType(p) {
          | Ok(ty) => Some(ty)
          | Error(_) => None
          }
        }
      } else {
        None
      }

      // Optional effects clause — v1.1 supports both flat and split forms.
      // parseEffectsClause returns a (memory_effects, caps) tuple.
      let (effects, caps) = if peek(p) == Effects {
        switch parseEffectsClause(p) {
        | Ok((mem, cs)) => (mem, cs)
        | Error(_) => (None, None)
        }
      } else {
        (None, None)
      }

      // Function body
      switch expect(p, LBrace) {
      | Ok() =>
        switch parseBlock(p) {
        | Ok(body) =>
          switch expect(p, RBrace) {
          | Ok() =>
            Ok({
              node: FunctionDecl({
                name,
                params,
                returnType,
                effects,
                caps, // v1.1: populated by parseEffectsClause (None for flat form)
                lifetimeConstraints: [],
                body,
              }),
              loc: startLoc,
            })
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse an import region declaration.
let parseImportRegion = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'import'
  let _ = expect(p, Region)
  switch expectIdent(p) {
  | Ok(regionName) =>
    let _ = expect(p, From)
    switch expectString(p) {
    | Ok(moduleName) =>
      let fields = []
      if peek(p) == LBrace {
        advance(p)
        let rec parseFields = () => {
          if peek(p) != RBrace {
            switch parseFieldDecl(p) {
            | Ok(field) =>
              let _ = Array.push(fields, field)
              parseFields()
            | Error(e) => Error(e)
            }
          } else {
            Ok()
          }
        }
        switch parseFields() {
        | Ok() =>
          let _ = expect(p, RBrace)
        | Error(e) => ignore(Error(e))
        }
      }
      Ok({node: ImportRegionDecl({regionName, moduleName, expectedFields: fields}), loc: startLoc})
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse an export region declaration.
let parseExportRegion = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'export'
  let _ = expect(p, Region)
  switch expectIdent(p) {
  | Ok(regionName) =>
    let _ = expect(p, Semicolon)
    Ok({node: ExportRegionDecl({regionName: regionName}), loc: startLoc})
  | Error(e) => Error(e)
  }
}

/// Parse a memory declaration.
let parseMemoryDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'memory'
  switch expectIdent(p) {
  | Ok(name) =>
    let _ = expect(p, LBrace)
    let initialPages = ref(0)
    let maximumPages = ref(None)
    let isShared = ref(false)
    let placements = []

    let rec parseMemBody = () => {
      switch peek(p) {
      | RBrace => Ok()
      | Initial =>
        advance(p)
        let _ = expect(p, Colon)
        switch expectInt(p) {
        | Ok(n) =>
          initialPages := n
          let _ = expect(p, Semicolon)
          parseMemBody()
        | Error(e) => Error(e)
        }
      | Maximum =>
        advance(p)
        let _ = expect(p, Colon)
        switch expectInt(p) {
        | Ok(n) =>
          maximumPages := Some(n)
          let _ = expect(p, Semicolon)
          parseMemBody()
        | Error(e) => Error(e)
        }
      | Shared =>
        advance(p)
        isShared := true
        let _ = expect(p, Semicolon)
        parseMemBody()
      | Place =>
        advance(p)
        let placeLoc = loc(p)
        switch expectIdent(p) {
        | Ok(regionName) =>
          let _ = expect(p, At)
          switch parseExpr(p) {
          | Ok(offset) =>
            let _ = expect(p, Semicolon)
            let _ = Array.push(placements, {node: {regionName, offset}, loc: placeLoc})
            parseMemBody()
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | _ => Error({message: "Unexpected token in memory declaration", loc: loc(p)})
      }
    }

    switch parseMemBody() {
    | Ok() =>
      let _ = expect(p, RBrace)
      Ok({
        node: MemoryDecl({
          name,
          initialPages: initialPages.contents,
          maximumPages: maximumPages.contents,
          isShared: isShared.contents,
          placements,
        }),
        loc: startLoc,
      })
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse a top-level invariant declaration.
let parseInvariantDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'invariant'
  switch expectIdent(p) {
  | Ok(name) =>
    let _ = expect(p, LBrace)
    let regions = []
    let proposition = ref(None)
    let tactic = ref(None)

    let rec parseInvBody = () => {
      switch peek(p) {
      | RBrace => Ok()
      | Across =>
        advance(p)
        let _ = expect(p, Colon)
        let rec parseRegionList = () => {
          switch expectIdent(p) {
          | Ok(r) =>
            let _ = Array.push(regions, r)
            if peek(p) == Comma {
              advance(p)
              parseRegionList()
            } else {
              Ok()
            }
          | Error(e) => Error(e)
          }
        }
        switch parseRegionList() {
        | Ok() =>
          let _ = expect(p, Semicolon)
          parseInvBody()
        | Error(e) => Error(e)
        }
      | Holds =>
        advance(p)
        let _ = expect(p, Colon)
        let holdsLoc = loc(p)
        switch parseExpr(p) {
        | Ok(prop) =>
          // Check if we consumed all the way to the semicolon
          if peek(p) == Semicolon {
            proposition := Some(prop)
            advance(p) // consume ;
            parseInvBody()
          } else {
            // Expression didn't consume the full proposition (e.g., forall ...)
            // Skip remaining tokens to semicolon
            while peek(p) != Semicolon && peek(p) != RBrace && peek(p) != EOF {
              advance(p)
            }
            let _ = expect(p, Semicolon)
            proposition := Some({node: BoolLit(true), loc: holdsLoc})
            parseInvBody()
          }
        | Error(_) =>
          // Complex proposition (e.g., forall ...) — skip to semicolon
          // and use a placeholder expression
          while peek(p) != Semicolon && peek(p) != RBrace && peek(p) != EOF {
            advance(p)
          }
          let _ = expect(p, Semicolon)
          proposition := Some({node: BoolLit(true), loc: holdsLoc})
          parseInvBody()
        }
      | Proof =>
        advance(p)
        let _ = expect(p, Colon)
        // Parse tactic
        switch peek(p) {
        | TacticBoundsCheck =>
          advance(p)
          tactic := Some(BoundsCheck)
        | TacticLinearity =>
          advance(p)
          tactic := Some(Linearity)
        | TacticLifetime =>
          advance(p)
          tactic := Some(Lifetime)
        | TacticAliasFreedom =>
          advance(p)
          tactic := Some(AliasFreedom)
        | TacticEffectPurity =>
          advance(p)
          tactic := Some(EffectPurity)
        | _ => ()
        }
        let _ = expect(p, Semicolon)
        parseInvBody()
      | _ => Error({message: "Unexpected token in invariant", loc: loc(p)})
      }
    }

    switch parseInvBody() {
    | Ok() =>
      let _ = expect(p, RBrace)
      switch proposition.contents {
      | Some(prop) =>
        Ok({
          node: InvariantDecl({name, regions, proposition: prop, proofTactic: tactic.contents}),
          loc: startLoc,
        })
      | None => Error({message: "Invariant missing 'holds' clause", loc: startLoc})
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

// ============================================================================
// Module Parsing (Top Level)
// ============================================================================

/// v1.1: Parse a top-level const declaration.
///
///   const_decl = 'const' identifier ':' field_type '=' literal ';'
///
/// The value MUST be a literal expression (Int/Float/String/Bool/Null). The
/// parser accepts any expression here to keep the grammar regular, and
/// `Checker.constValueIsLiteral` rejects non-literals at check time with a
/// more informative error than a parse error could give. This also keeps
/// the door open for a v1.2+ relaxation to allow const-folded expressions.
let parseConstDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume 'const'

  switch expectIdent(p) {
  | Ok(name) =>
    switch expect(p, Colon) {
    | Ok() =>
      switch parseFieldType(p) {
      | Ok(constType) =>
        switch expect(p, Eq) {
        | Ok() =>
          switch parseExpr(p) {
          | Ok(value) =>
            switch expect(p, Semicolon) {
            | Ok() =>
              Ok({
                node: ConstDecl({name, constType, value}),
                loc: startLoc,
              })
            | Error(e) => Error(e)
            }
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

// ============================================================================
// v1.2 / L13 — Module Isolation
// ============================================================================
//
// L13 adds three contextual keywords — `module`, `isolated`, `private_memory`,
// `boundary` — that are lexed as plain `Ident(...)` and recognised here by
// the parser when they appear at a declaration position. This follows the
// contextual-reservation policy documented in Lexer.res and
// spec/L13-L16-reserved-syntax.adoc; the global lexer reservation attempted
// earlier collided with field names like `state` in real .twasm sources.
//
// Scope:
//   * `module Name isolated { ... }` is the ONLY legal placement for
//     `private_memory` and `boundary` decls. A bare `boundary ...;` at the
//     top level produces a parse error pointing at L13.
//   * An isolated module's body may contain regular declarations
//     (region / fn / import / export / memory / invariant / const) plus
//     nested boundary decls and at most one private_memory.

/// v1.2 / L13: parse a private_memory declaration inside an isolated module.
///
///   private_memory_decl = 'private_memory' identifier '{'
///                             'initial' ':' positive_integer ';'
///                             ['maximum' ':' positive_integer ';']
///                         '}'
let parsePrivateMemoryDecl = (p: parserState): result<Ast.located<Ast.privateMemoryDecl>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("private_memory")
  switch expectIdent(p) {
  | Ok(name) =>
    switch expect(p, LBrace) {
    | Ok() =>
      let initialPages = ref(0)
      let maximumPages = ref(None)
      let rec parsePmBody = () => {
        switch peek(p) {
        | RBrace => Ok()
        | Initial =>
          advance(p)
          let _ = expect(p, Colon)
          switch expectInt(p) {
          | Ok(n) =>
            initialPages := n
            let _ = expect(p, Semicolon)
            parsePmBody()
          | Error(e) => Error(e)
          }
        | Maximum =>
          advance(p)
          let _ = expect(p, Colon)
          switch expectInt(p) {
          | Ok(n) =>
            maximumPages := Some(n)
            let _ = expect(p, Semicolon)
            parsePmBody()
          | Error(e) => Error(e)
          }
        | _ => Error({message: "Unexpected token in private_memory block", loc: loc(p)})
        }
      }
      switch parsePmBody() {
      | Ok() =>
        let _ = expect(p, RBrace)
        Ok({
          node: {
            name,
            initialPages: initialPages.contents,
            maximumPages: maximumPages.contents,
          },
          loc: startLoc,
        })
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// v1.2 / L13: parse a boundary declaration.
///
///   boundary_decl = 'boundary' identifier ':' ('import' | 'export')
///                   'region' identifier ';'
let parseBoundaryDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("boundary")
  switch expectIdent(p) {
  | Ok(name) =>
    switch expect(p, Colon) {
    | Ok() =>
      let direction = switch peek(p) {
      | Import =>
        advance(p)
        Ok(BoundaryImport)
      | Export =>
        advance(p)
        Ok(BoundaryExport)
      | _ =>
        Error({message: "Boundary direction must be 'import' or 'export'", loc: loc(p)})
      }
      switch direction {
      | Ok(dir) =>
        switch expect(p, Region) {
        | Ok() =>
          switch expectIdent(p) {
          | Ok(regionName) =>
            switch expect(p, Semicolon) {
            | Ok() =>
              Ok({
                node: BoundaryDecl({name, direction: dir, regionName}),
                loc: startLoc,
              })
            | Error(e) => Error(e)
            }
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

// ============================================================================
// v1.3 / L14 — Session Protocols
// ============================================================================
//
// Session, state, transition, consume, dual are contextual keywords. They
// appear here as Ident(...) and are matched by string inside parseSessionDecl.
// `yield` reuses the existing global `Yield` token from v1.1 block-if; it has
// the same surface meaning ("produce a value") in both contexts.

/// Parse one state declaration inside a `session` block.
///
///   state_decl = 'state' identifier [':' field_type] ';'
let parseSessionStateDecl = (p: parserState): result<Ast.located<Ast.sessionStateDecl>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("state")
  switch expectIdent(p) {
  | Ok(name) =>
    let payload = if peek(p) == Colon {
      advance(p)
      switch parseFieldType(p) {
      | Ok(t) => Ok(Some(t))
      | Error(e) => Error(e)
      }
    } else {
      Ok(None)
    }
    switch payload {
    | Ok(pl) =>
      switch expect(p, Semicolon) {
      | Ok() => Ok({node: {name, payload: pl}, loc: startLoc})
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse one transition declaration inside a `session` block.
///
///   transition_decl = 'transition' identifier ':' 'consume' identifier
///                     '->' 'yield' identifier ';'
let parseSessionTransitionDecl = (
  p: parserState,
): result<Ast.located<Ast.sessionTransitionDecl>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("transition")
  switch expectIdent(p) {
  | Ok(name) =>
    switch expect(p, Colon) {
    | Ok() =>
      // 'consume' is a contextual keyword — Ident("consume")
      switch peek(p) {
      | Ident("consume") =>
        advance(p)
        switch expectIdent(p) {
        | Ok(consumes) =>
          switch expect(p, Arrow) {
          | Ok() =>
            // 'yield' is the global Yield token
            switch peek(p) {
            | Yield =>
              advance(p)
              switch expectIdent(p) {
              | Ok(produces) =>
                switch expect(p, Semicolon) {
                | Ok() =>
                  Ok({node: {name, consumes, produces}, loc: startLoc})
                | Error(e) => Error(e)
                }
              | Error(e) => Error(e)
              }
            | _ =>
              Error({
                message: "Expected 'yield' in transition (L14)",
                loc: loc(p),
              })
            }
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      | _ =>
        Error({
          message: "Expected 'consume' after transition name (L14)",
          loc: loc(p),
        })
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// Parse a session declaration.
///
///   session_decl = 'session' identifier '{' { state_decl } { transition_decl }
///                  ['dual' ':' identifier ';'] '}'
///
/// State, transition, and dual entries may appear in any order; the parser
/// dispatches on the leading contextual keyword for each.
let parseSessionDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("session")
  switch expectIdent(p) {
  | Ok(name) =>
    switch expect(p, LBrace) {
    | Ok() =>
      let states: array<Ast.located<Ast.sessionStateDecl>> = []
      let transitions: array<Ast.located<Ast.sessionTransitionDecl>> = []
      let dualName = ref(None)
      let rec parseBody = () => {
        switch peek(p) {
        | RBrace => Ok()
        | EOF =>
          Error({
            message: "Unexpected EOF inside 'session " ++ name ++ " { ... }' body",
            loc: loc(p),
          })
        | Ident("state") =>
          switch parseSessionStateDecl(p) {
          | Ok(s) =>
            let _ = Array.push(states, s)
            parseBody()
          | Error(e) => Error(e)
          }
        | Ident("transition") =>
          switch parseSessionTransitionDecl(p) {
          | Ok(t) =>
            let _ = Array.push(transitions, t)
            parseBody()
          | Error(e) => Error(e)
          }
        | Ident("dual") =>
          advance(p)
          switch expect(p, Colon) {
          | Ok() =>
            switch expectIdent(p) {
            | Ok(d) =>
              switch expect(p, Semicolon) {
              | Ok() =>
                dualName := Some(d)
                parseBody()
              | Error(e) => Error(e)
              }
            | Error(e) => Error(e)
            }
          | Error(e) => Error(e)
          }
        | _ =>
          Error({
            message: "Unexpected token in session body — expected 'state', 'transition', 'dual', or '}'",
            loc: loc(p),
          })
        }
      }
      switch parseBody() {
      | Ok() =>
        let _ = expect(p, RBrace)
        Ok({
          node: SessionDecl({
            name,
            states,
            transitions,
            dualName: dualName.contents,
          }),
          loc: startLoc,
        })
      | Error(e) => Error(e)
      }
    | Error(e) => Error(e)
    }
  | Error(e) => Error(e)
  }
}

/// v1.4 / L15 — parse a capability declaration.
///
///   capability_decl = 'capability' identifier ';' ;
///
/// `capability` is a contextual keyword — arrives as Ident("capability").
/// Legal at top level and inside an isolated module body. The checker
/// enforces L15-A (distinct) and L15-B (well-scoped) on the collected set.
let parseCapabilityDecl = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("capability")
  switch expectIdent(p) {
  | Error(e) => Error(e)
  | Ok(name) =>
    switch expect(p, Semicolon) {
    | Error(e) => Error(e)
    | Ok() =>
      Ok({
        node: CapabilityDecl({name: name}),
        loc: startLoc,
      })
    }
  }
}

/// Parse a top-level declaration.
///
/// v1.2 / L13: also recognises `module Name isolated { ... }` via the
/// Ident("module") contextual branch, and rejects stray `boundary` or
/// `private_memory` at top level with a pointer to L13.
///
/// v1.3 / L14: also recognises `session Name { ... }` via Ident("session").
///
/// v1.4 / L15: also recognises `capability NAME;` via Ident("capability").
/// Rejects stray `grant` / `relinquish` / `requires_caps` at top level —
/// those remain reserved-but-not-live at v1.4.
let rec parseDeclaration = (p: parserState): result<Ast.located<Ast.declaration>> => {
  switch peek(p) {
  | Region => parseRegionDecl(p)
  | Import => parseImportRegion(p)
  | Export => parseExportRegion(p)
  | Fn => parseFunctionDecl(p)
  | Memory => parseMemoryDecl(p)
  | Invariant => parseInvariantDecl(p)
  | Const => parseConstDecl(p) // v1.1
  | Ident("module") => parseIsolatedModule(p) // v1.2 / L13
  | Ident("session") => parseSessionDecl(p) // v1.3 / L14
  | Ident("capability") => parseCapabilityDecl(p) // v1.4 / L15
  | Ident("boundary") =>
    Error({
      message: "'boundary' may only appear inside 'module Name isolated { ... }' (L13 — see spec/L13-L16-reserved-syntax.adoc)",
      loc: loc(p),
    })
  | Ident("private_memory") =>
    Error({
      message: "'private_memory' may only appear inside 'module Name isolated { ... }' (L13 — see spec/L13-L16-reserved-syntax.adoc)",
      loc: loc(p),
    })
  | Ident("state")
  | Ident("transition")
  | Ident("dual") =>
    Error({
      message: "session-body keyword used outside a 'session Name { ... }' block (L14 — see spec/L13-L16-reserved-syntax.adoc)",
      loc: loc(p),
    })
  | Ident("grant")
  | Ident("relinquish")
  | Ident("requires_caps") =>
    Error({
      message: "'grant' / 'relinquish' / 'requires_caps' are reserved L15 keywords but not live at v1.4 (see spec/L13-L16-reserved-syntax.adoc — only 'capability' is live in v1.4)",
      loc: loc(p),
    })
  | _ =>
    Error({
      message: "Expected declaration (region, import, export, fn, memory, invariant, const, module, session, capability)",
      loc: loc(p),
    })
  }
}

/// v1.2 / L13: parse an isolated module declaration.
///
///   module_decl_isolated = 'module' identifier 'isolated' '{'
///                              [private_memory_decl]
///                              { declaration | boundary_decl }
///                          '}'
///
/// The body may contain at most one private_memory declaration (typically
/// first). Boundary decls and regular declarations may be interleaved. The
/// contextual keywords `module`, `isolated`, `private_memory`, `boundary`
/// are not reserved at the lexer level — they arrive here as Ident(...).
and parseIsolatedModule = (p: parserState): result<Ast.located<Ast.declaration>> => {
  let startLoc = loc(p)
  advance(p) // consume Ident("module")
  switch expectIdent(p) {
  | Ok(name) =>
    switch peek(p) {
    | Ident("isolated") =>
      advance(p)
      switch expect(p, LBrace) {
      | Ok() =>
        let privateMemory = ref(None)
        let declarations: array<Ast.located<Ast.declaration>> = []
        let rec parseBody = () => {
          switch peek(p) {
          | RBrace => Ok()
          | EOF =>
            Error({
              message: "Unexpected EOF inside 'module " ++ name ++ " isolated { ... }' body",
              loc: loc(p),
            })
          | Ident("private_memory") =>
            switch privateMemory.contents {
            | Some(_) =>
              Error({
                message: "Isolated module '" ++
                name ++ "' may declare at most one private_memory",
                loc: loc(p),
              })
            | None =>
              switch parsePrivateMemoryDecl(p) {
              | Ok(pm) =>
                privateMemory := Some(pm)
                parseBody()
              | Error(e) => Error(e)
              }
            }
          | Ident("boundary") =>
            switch parseBoundaryDecl(p) {
            | Ok(decl) =>
              let _ = Array.push(declarations, decl)
              parseBody()
            | Error(e) => Error(e)
            }
          | Ident("capability") =>
            // v1.4 / L15: capability decls legal inside isolated modules
            switch parseCapabilityDecl(p) {
            | Ok(decl) =>
              let _ = Array.push(declarations, decl)
              parseBody()
            | Error(e) => Error(e)
            }
          | _ =>
            switch parseDeclaration(p) {
            | Ok(decl) =>
              let _ = Array.push(declarations, decl)
              parseBody()
            | Error(e) => Error(e)
            }
          }
        }
        switch parseBody() {
        | Ok() =>
          let _ = expect(p, RBrace)
          Ok({
            node: ModuleIsolatedDecl({
              name,
              privateMemory: privateMemory.contents,
              declarations,
            }),
            loc: startLoc,
          })
        | Error(e) => Error(e)
        }
      | Error(e) => Error(e)
      }
    | _ =>
      Error({
        message: "Expected 'isolated' after module name '" ++
        name ++
        "' (L13 — `module " ++
        name ++ " isolated { ... }`)",
        loc: loc(p),
      })
    }
  | Error(e) => Error(e)
  }
}

/// Parse a complete typed-wasm module.
let parseModule = (source: string): result<Ast.module_> => {
  let p = make(source)
  let declarations = []

  let rec loop = () => {
    if peek(p) != EOF {
      switch parseDeclaration(p) {
      | Ok(decl) =>
        let _ = Array.push(declarations, decl)
        loop()
      | Error(e) => Error(e)
      }
    } else {
      Ok({declarations: declarations})
    }
  }

  loop()
}
