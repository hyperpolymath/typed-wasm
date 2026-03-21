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
    p.tokens[p.pos]
  } else {
    {value: EOF, loc: {line: 0, col: 0}}
  }
}

/// Peek at the current token value.
let peek = (p: parserState): Lexer.token => {
  (current(p)).value
}

/// Get current location.
let loc = (p: parserState): Lexer.loc => {
  (current(p)).loc
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

/// Expect an identifier. Returns the name.
let expectIdent = (p: parserState): result<string> => {
  switch peek(p) {
  | Ident(name) =>
    advance(p)
    Ok(name)
  | _ => Error({message: "Expected identifier", loc: loc(p)})
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
      switch expect(p, RAngle) {
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
      switch expect(p, RAngle) {
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
      switch expect(p, RAngle) {
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
      switch expect(p, RAngle) {
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
          | Ok() => Ok({node: ArrayFieldType({node: Primitive(prim), loc: startLoc}, sizeExpr), loc: startLoc})
          | Error(e) => Error(e)
          }
        | Error(e) => Error(e)
        }
      } else {
        Ok({node: Primitive(prim), loc: startLoc})
      }
    | Error(_) =>
      Error({message: "Expected field type", loc: startLoc})
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
      let _ = expect(p, RAngle)
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
    let rec loop = (left) => {
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
let parseRegionTarget = (p: parserState): result<Ast.regionTarget> => {
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
let parseFieldPath = (p: parserState): result<array<Ast.fieldPathSegment>> => {
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
let rec parseStatement = (p: parserState): result<Ast.located<Ast.statement>> => {
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
        | Ok() => let _ = expect(p, RBrace)
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
        switch parseFieldType(p) {
        | Ok(ty) => Some(ty)
        | Error(_) => None
        }
      } else {
        None
      }
      switch expect(p, Eq) {
      | Ok() =>
        switch parseExpr(p) {
        | Ok(init) =>
          let _ = expect(p, Semicolon)
          Ok({node: LetStmt({isMutable: isMut, name, typeAnnotation: typeAnn, initializer: init}), loc: startLoc})
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
            Ok({node: IfStmt({condition: cond, thenBranch: thenBody, elseBranch: elseBody}), loc: startLoc})
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

  // Default: expression statement
  | _ =>
    switch parseExpr(p) {
    | Ok(expr) =>
      let _ = expect(p, Semicolon)
      Ok({node: ExprStmt(expr), loc: startLoc})
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
            let _ = Array.push(constraints, {node: PredicateConstraint("constraint", [expr]), loc: startLoc})
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
                  let _ = Array.push(invariants, {node: {name: invName, proposition: prop}, loc: startLoc})
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
let parseEffects = (p: parserState): result<array<Ast.located<Ast.effect>>> => {
  let effects = []
  advance(p) // consume 'effects'
  let _ = expect(p, LBrace)
  let rec loop = () => {
    if peek(p) != RBrace {
      let startLoc = loc(p)
      let eff = switch peek(p) {
      | EffRead => advance(p); Ok(ReadEffect)
      | EffWrite => advance(p); Ok(WriteEffect)
      | EffAlloc => advance(p); Ok(AllocEffect)
      | EffFree => advance(p); Ok(FreeEffect)
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
      | Ok(e) =>
        let _ = Array.push(effects, {node: e, loc: startLoc})
        if peek(p) == Comma {
          advance(p)
        }
        loop()
      | Error(e) => Error(e)
      }
    } else {
      Ok()
    }
  }
  switch loop() {
  | Ok() =>
    let _ = expect(p, RBrace)
    Ok(effects)
  | Error(e) => Error(e)
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
            | AmpMut => advance(p); MutableBorrow
            | Ampersand => advance(p); SharedBorrow
            | Own => advance(p); Owning
            | _ => SharedBorrow
            }
            let _ = expect(p, Region)
            let _ = expect(p, LAngle)
            switch expectIdent(p) {
            | Ok(regionName) =>
              let _ = expect(p, RAngle)
              let _ = Array.push(params, {
                node: {name: paramName, paramType: {node: RegionHandleParam(mode, regionName), loc: paramLoc}},
                loc: paramLoc,
              })
              if peek(p) == Comma {
                advance(p)
              }
              parseParams()
            | Error(e) => Error(e)
            }
          | _ =>
            switch parseFieldType(p) {
            | Ok(ty) =>
              let _ = Array.push(params, {
                node: {name: paramName, paramType: {node: FieldParam(ty.node), loc: paramLoc}},
                loc: paramLoc,
              })
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

      // Optional return type
      let returnType = if peek(p) == Arrow {
        advance(p)
        switch parseFieldType(p) {
        | Ok(ty) => Some(ty)
        | Error(_) => None
        }
      } else {
        None
      }

      // Optional effects clause
      let effects = if peek(p) == Effects {
        switch parseEffects(p) {
        | Ok(effs) => Some(effs)
        | Error(_) => None
        }
      } else {
        None
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
        | Ok() => let _ = expect(p, RBrace)
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
        switch parseExpr(p) {
        | Ok(prop) =>
          proposition := Some(prop)
          let _ = expect(p, Semicolon)
          parseInvBody()
        | Error(e) => Error(e)
        }
      | Proof =>
        advance(p)
        let _ = expect(p, Colon)
        // Parse tactic
        switch peek(p) {
        | TacticBoundsCheck => advance(p); tactic := Some(BoundsCheck)
        | TacticLinearity => advance(p); tactic := Some(Linearity)
        | TacticLifetime => advance(p); tactic := Some(Lifetime)
        | TacticAliasFreedom => advance(p); tactic := Some(AliasFreedom)
        | TacticEffectPurity => advance(p); tactic := Some(EffectPurity)
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

/// Parse a top-level declaration.
let parseDeclaration = (p: parserState): result<Ast.located<Ast.declaration>> => {
  switch peek(p) {
  | Region => parseRegionDecl(p)
  | Import => parseImportRegion(p)
  | Export => parseExportRegion(p)
  | Fn => parseFunctionDecl(p)
  | Memory => parseMemoryDecl(p)
  | Invariant => parseInvariantDecl(p)
  | _ => Error({message: "Expected declaration (region, import, export, fn, memory, invariant)", loc: loc(p)})
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
