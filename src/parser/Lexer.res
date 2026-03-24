// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Lexer.res — Tokenizer for typed-wasm (.twasm) surface syntax.
//
// Produces a stream of tokens from raw source text. Each token carries
// its source location (line, column) for error reporting.
//
// The lexer handles:
//   - Keywords (region, fn, let, if, etc.)
//   - Region operations (region.get, region.set, region.scan, region.alloc, region.free)
//   - Pointer kinds (ptr, ref, unique, opt, own)
//   - Effect labels (Read, Write, Alloc, Free, ReadRegion, WriteRegion)
//   - Proof tactics (bounds_check, linearity, lifetime, alias_freedom, effect_purity)
//   - Primitive types (i8, i16, i32, i64, u8, u16, u32, u64, f32, f64, bool)
//   - Symbols, literals, identifiers, and comments

/// Source location for error reporting.
type loc = {
  line: int,
  col: int,
}

/// Token with source location.
type located<'a> = {
  value: 'a,
  loc: loc,
}

/// All token types in the typed-wasm grammar.
type token =
  // --- Literals ---
  | IntLiteral(int)
  | FloatLiteral(float)
  | StringLiteral(string)
  | True
  | False
  | Null
  // --- Identifiers ---
  | Ident(string)
  // --- Keywords: declarations ---
  | Region
  | Import
  | Export
  | From
  | Memory
  | Fn
  | Let
  | Mut
  | If
  | Else
  | While
  | Return
  | Where
  | Void
  | Invariant
  | Across
  | Holds
  | Place
  | At
  | Initial
  | Maximum
  | Shared
  | Align
  | Union
  // --- Region operations ---
  | RegionGet
  | RegionSet
  | RegionScan
  | RegionAlloc
  | RegionFree
  // --- Pointer kinds ---
  | Ptr
  | Ref
  | Unique
  | Opt
  | Own
  // --- Effects ---
  | Effects
  | EffRead
  | EffWrite
  | EffAlloc
  | EffFree
  | EffReadRegion
  | EffWriteRegion
  // --- Lifetimes ---
  | Lifetime
  | LifetimeName(string) // 'name
  // --- Proofs ---
  | Proof
  | Given
  | Show
  | By
  | StaticAssert
  | TacticBoundsCheck
  | TacticLinearity
  | TacticLifetime
  | TacticAliasFreedom
  | TacticEffectPurity
  | TacticInduction
  | TacticRewrite
  // --- Primitive types ---
  | TyI8
  | TyI16
  | TyI32
  | TyI64
  | TyU8
  | TyU16
  | TyU32
  | TyU64
  | TyF32
  | TyF64
  | TyBool
  // --- Intrinsics ---
  | Sizeof
  | Offsetof
  | Typeof
  | IsValid
  | IsNull
  | Cast
  // --- Symbols ---
  | LParen
  | RParen
  | LBrace
  | RBrace
  | LBracket
  | RBracket
  | LAngle
  | RAngle
  | Comma
  | Semicolon
  | Colon
  | ColonColon // ::
  | Dot
  | Arrow // ->
  | Ampersand // &
  | AmpMut // &mut
  | Dollar // $
  | Pipe // |
  | Question // ?
  | Bang // !
  | Tilde // ~
  | Plus
  | Minus
  | Star
  | Slash
  | Percent
  | Eq // =
  | EqEq // ==
  | BangEq // !=
  | LtEq // <=
  | GtEq // >=
  | AmpAmp // &&
  | PipePipe // ||
  | Caret // ^
  | LShift // <<
  | RShift // >>
  // At is defined above as keyword — also used for @ symbol
  // --- Special ---
  | EOF

/// Lexer state.
type lexerState = {
  source: string,
  mutable pos: int,
  mutable line: int,
  mutable col: int,
}

/// Create a new lexer from source text.
let make = (source: string): lexerState => {
  source,
  pos: 0,
  line: 1,
  col: 1,
}

/// Check if we've reached the end of input.
let isAtEnd = (l: lexerState): bool => {
  l.pos >= String.length(l.source)
}

/// Peek at the current character without consuming.
let peek = (l: lexerState): option<char> => {
  if isAtEnd(l) {
    None
  } else {
    Some(String.get(l.source, l.pos))
  }
}

/// Peek at the next character (lookahead 1).
let peekNext = (l: lexerState): option<char> => {
  if l.pos + 1 >= String.length(l.source) {
    None
  } else {
    Some(String.get(l.source, l.pos + 1))
  }
}

/// Consume and return the current character.
let advance = (l: lexerState): char => {
  let ch = String.get(l.source, l.pos)
  l.pos = l.pos + 1
  if ch == '\n' {
    l.line = l.line + 1
    l.col = 1
  } else {
    l.col = l.col + 1
  }
  ch
}

/// Get the current source location.
let currentLoc = (l: lexerState): loc => {
  {line: l.line, col: l.col}
}

/// Skip whitespace and comments.
let rec skipWhitespaceAndComments = (l: lexerState): unit => {
  if !isAtEnd(l) {
    switch peek(l) {
    | Some(' ') | Some('\t') | Some('\r') | Some('\n') =>
      let _ = advance(l)
      skipWhitespaceAndComments(l)
    | Some('/') =>
      switch peekNext(l) {
      | Some('/') =>
        // Line comment: skip to end of line
        let _ = advance(l) // consume /
        let _ = advance(l) // consume /
        let rec skipLine = () => {
          if !isAtEnd(l) {
            switch peek(l) {
            | Some('\n') =>
              let _ = advance(l)
              ()
            | Some(_) =>
              let _ = advance(l)
              skipLine()
            | None => ()
            }
          }
        }
        skipLine()
        skipWhitespaceAndComments(l)
      | Some('*') =>
        // Block comment: skip to */
        let _ = advance(l) // consume /
        let _ = advance(l) // consume *
        let rec skipBlock = () => {
          if !isAtEnd(l) {
            switch peek(l) {
            | Some('*') =>
              let _ = advance(l)
              switch peek(l) {
              | Some('/') =>
                let _ = advance(l)
                ()
              | _ => skipBlock()
              }
            | Some(_) =>
              let _ = advance(l)
              skipBlock()
            | None => ()
            }
          }
        }
        skipBlock()
        skipWhitespaceAndComments(l)
      | _ => ()
      }
    | _ => ()
    }
  }
}

/// Check if a character is alphabetic or underscore.
let isAlpha = (ch: char): bool => {
  (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
}

/// Check if a character is a digit.
let isDigit = (ch: char): bool => {
  ch >= '0' && ch <= '9'
}

/// Check if a character is alphanumeric or underscore.
let isAlphaNumeric = (ch: char): bool => {
  isAlpha(ch) || isDigit(ch)
}

/// Read an identifier or keyword.
let readIdentOrKeyword = (l: lexerState): token => {
  let start = l.pos
  while !isAtEnd(l) && isAlphaNumeric(Option.getOr(peek(l), ' ')) {
    let _ = advance(l)
  }
  let text = String.sub(l.source, start, l.pos - start)

  // Check for region.xxx compound tokens
  if text == "region" && !isAtEnd(l) && peek(l) == Some('.') {
    let savedPos = l.pos
    let savedLine = l.line
    let savedCol = l.col
    let _ = advance(l) // consume .
    let methodStart = l.pos
    while !isAtEnd(l) && isAlphaNumeric(Option.getOr(peek(l), ' ')) {
      let _ = advance(l)
    }
    let method = String.sub(l.source, methodStart, l.pos - methodStart)
    switch method {
    | "get" => RegionGet
    | "set" => RegionSet
    | "scan" => RegionScan
    | "alloc" => RegionAlloc
    | "free" => RegionFree
    | _ =>
      // Not a region method — backtrack
      l.pos = savedPos
      l.line = savedLine
      l.col = savedCol
      Region
    }
  } else {
    // Keyword lookup
    switch text {
    | "region" => Region
    | "import" => Import
    | "export" => Export
    | "from" => From
    | "memory" => Memory
    | "fn" => Fn
    | "let" => Let
    | "mut" => Mut
    | "if" => If
    | "else" => Else
    | "while" => While
    | "return" => Return
    | "where" => Where
    | "void" => Void
    | "invariant" => Invariant
    | "across" => Across
    | "holds" => Holds
    | "place" => Place
    | "at" => At
    | "initial" => Initial
    | "maximum" => Maximum
    | "shared" => Shared
    | "align" => Align
    | "union" => Union
    // Pointer kinds
    | "ptr" => Ptr
    | "ref" => Ref
    | "unique" => Unique
    | "opt" => Opt
    | "own" => Own
    // Effects
    | "effects" => Effects
    | "Read" => EffRead
    | "Write" => EffWrite
    | "Alloc" => EffAlloc
    | "Free" => EffFree
    | "ReadRegion" => EffReadRegion
    | "WriteRegion" => EffWriteRegion
    // Lifetimes
    | "lifetime" => Lifetime
    // Proofs
    | "proof" => Proof
    | "given" => Given
    | "show" => Show
    | "by" => By
    | "static_assert" => StaticAssert
    | "bounds_check" => TacticBoundsCheck
    | "linearity" => TacticLinearity
    | "alias_freedom" => TacticAliasFreedom
    | "effect_purity" => TacticEffectPurity
    | "induction" => TacticInduction
    | "rewrite" => TacticRewrite
    // Primitive types
    | "i8" => TyI8
    | "i16" => TyI16
    | "i32" => TyI32
    | "i64" => TyI64
    | "u8" => TyU8
    | "u16" => TyU16
    | "u32" => TyU32
    | "u64" => TyU64
    | "f32" => TyF32
    | "f64" => TyF64
    | "bool" => TyBool
    // Boolean literals
    | "true" => True
    | "false" => False
    | "null" => Null
    // Intrinsics
    | "sizeof" => Sizeof
    | "offsetof" => Offsetof
    | "typeof" => Typeof
    | "is_valid" => IsValid
    | "is_null" => IsNull
    | "cast" => Cast
    // Default: identifier
    | _ => Ident(text)
    }
  }
}

/// Read a number literal (integer or float).
let readNumber = (l: lexerState): token => {
  let start = l.pos
  let isNegative = peek(l) == Some('-')
  if isNegative {
    let _ = advance(l)
  }

  while !isAtEnd(l) && isDigit(Option.getOr(peek(l), ' ')) {
    let _ = advance(l)
  }

  // Check for float
  if !isAtEnd(l) && peek(l) == Some('.') && isDigit(Option.getOr(peekNext(l), ' ')) {
    let _ = advance(l) // consume .
    while !isAtEnd(l) && isDigit(Option.getOr(peek(l), ' ')) {
      let _ = advance(l)
    }
    let text = String.sub(l.source, start, l.pos - start)
    FloatLiteral(Float.fromString(text)->Option.getOr(0.0))
  } else {
    let text = String.sub(l.source, start, l.pos - start)
    IntLiteral(Int.fromString(text)->Option.getOr(0))
  }
}

/// Read a string literal (double-quoted).
let readString = (l: lexerState): token => {
  let _ = advance(l) // consume opening "
  let start = l.pos
  while !isAtEnd(l) && peek(l) != Some('"') {
    let _ = advance(l)
  }
  let text = String.sub(l.source, start, l.pos - start)
  if !isAtEnd(l) {
    let _ = advance(l) // consume closing "
  }
  StringLiteral(text)
}

/// Get the next token from the source.
let nextToken = (l: lexerState): located<token> => {
  skipWhitespaceAndComments(l)

  if isAtEnd(l) {
    {value: EOF, loc: currentLoc(l)}
  } else {
    let startLoc = currentLoc(l)
    let ch = Option.getOr(peek(l), ' ')

    let tok = if isAlpha(ch) {
      readIdentOrKeyword(l)
    } else if isDigit(ch) {
      readNumber(l)
    } else if ch == '"' {
      readString(l)
    } else if ch == '\'' {
      // Lifetime name: 'identifier
      let _ = advance(l) // consume '
      if ch == 's' && !isAtEnd(l) {
        // Could be 'static or 'name
        let nameStart = l.pos
        while !isAtEnd(l) && isAlphaNumeric(Option.getOr(peek(l), ' ')) {
          let _ = advance(l)
        }
        let name = String.sub(l.source, nameStart, l.pos - nameStart)
        LifetimeName(name)
      } else {
        let nameStart = l.pos
        while !isAtEnd(l) && isAlphaNumeric(Option.getOr(peek(l), ' ')) {
          let _ = advance(l)
        }
        let name = String.sub(l.source, nameStart, l.pos - nameStart)
        LifetimeName(name)
      }
    } else {
      // Symbols
      let _ = advance(l)
      switch ch {
      | '(' => LParen
      | ')' => RParen
      | '{' => LBrace
      | '}' => RBrace
      | '[' => LBracket
      | ']' => RBracket
      | ',' => Comma
      | ';' => Semicolon
      | '.' => Dot
      | '$' => Dollar
      | '?' => Question
      | '~' => Tilde
      | '^' => Caret
      | '@' => At
      | '%' => Percent
      | '+' => Plus
      | '*' => Star
      | '/' => Slash
      | ':' =>
        if !isAtEnd(l) && peek(l) == Some(':') {
          let _ = advance(l)
          ColonColon
        } else {
          Colon
        }
      | '-' =>
        if !isAtEnd(l) && peek(l) == Some('>') {
          let _ = advance(l)
          Arrow
        } else if !isAtEnd(l) && isDigit(Option.getOr(peek(l), ' ')) {
          // Negative number
          l.pos = l.pos - 1
          l.col = l.col - 1
          readNumber(l)
        } else {
          Minus
        }
      | '=' =>
        if !isAtEnd(l) && peek(l) == Some('=') {
          let _ = advance(l)
          EqEq
        } else {
          Eq
        }
      | '!' =>
        if !isAtEnd(l) && peek(l) == Some('=') {
          let _ = advance(l)
          BangEq
        } else {
          Bang
        }
      | '<' =>
        if !isAtEnd(l) && peek(l) == Some('=') {
          let _ = advance(l)
          LtEq
        } else if !isAtEnd(l) && peek(l) == Some('<') {
          let _ = advance(l)
          LShift
        } else {
          LAngle
        }
      | '>' =>
        if !isAtEnd(l) && peek(l) == Some('=') {
          let _ = advance(l)
          GtEq
        } else if !isAtEnd(l) && peek(l) == Some('>') {
          let _ = advance(l)
          RShift
        } else {
          RAngle
        }
      | '&' =>
        if !isAtEnd(l) && peek(l) == Some('&') {
          let _ = advance(l)
          AmpAmp
        } else if !isAtEnd(l) && peek(l) == Some('m') {
          // Check for &mut
          let savedPos = l.pos
          let savedCol = l.col
          let savedLine = l.line
          let _ = advance(l) // m
          if !isAtEnd(l) && peek(l) == Some('u') {
            let _ = advance(l) // u
            if !isAtEnd(l) && peek(l) == Some('t') {
              let _ = advance(l) // t
              // Check next char is not alphanumeric (so &mutable doesn't match)
              if isAtEnd(l) || !isAlphaNumeric(Option.getOr(peek(l), ' ')) {
                AmpMut
              } else {
                l.pos = savedPos
                l.col = savedCol
                l.line = savedLine
                Ampersand
              }
            } else {
              l.pos = savedPos
              l.col = savedCol
              l.line = savedLine
              Ampersand
            }
          } else {
            l.pos = savedPos
            l.col = savedCol
            l.line = savedLine
            Ampersand
          }
        } else {
          Ampersand
        }
      | '|' =>
        if !isAtEnd(l) && peek(l) == Some('|') {
          let _ = advance(l)
          PipePipe
        } else {
          Pipe
        }
      | _ => Ident(String.make(1, ch)) // Unknown character as ident
      }
    }

    {value: tok, loc: startLoc}
  }
}

/// Tokenize entire source into a list of located tokens.
let tokenize = (source: string): array<located<token>> => {
  let l = make(source)
  let tokens = []
  let rec loop = () => {
    let tok = nextToken(l)
    let _ = Array.push(tokens, tok)
    if tok.value != EOF {
      loop()
    }
  }
  loop()
  tokens
}
