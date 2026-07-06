// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! Minimal .twasm text parser for codegen v0.
//!
//! This module provides a Rust-native parser for the typed-wasm surface syntax
//! as a stopgap until the AffineScript front-end (ADR-0004, issue #127) lands.
//! It is intentionally limited to the subset needed by paint-type schemas and
//! example-01, not the full .twasm language.
//!
//! This parser does NOT duplicate the full AffineScript front-end — it only handles
//! the specific schemas needed to unblock paint-type#39 and demonstrate the
//! codegen path. Full .twasm parsing remains deferred to the AffineScript front-end.

use crate::{Field, FieldTy, Memory, Module, PtrKind, Region, Scalar, Wty};
use std::collections::HashMap;

/// Parse a .twasm source file into a Module IR.
pub fn parse_module(src: &str) -> Result<Module, String> {
    let parser = Parser::new(src);
    parser.parse_module()
}

/// A simple hand-written parser for .twasm syntax.
struct Parser<'a> {
    src: &'a str,
    pos: usize,
    regions: Vec<Region>,
    region_map: HashMap<String, usize>,
    memory: Option<Memory>,
    imports: Vec<crate::Import>,
    funcs: Vec<crate::Func>,
    ownership: Vec<(usize, Vec<crate::Ownership>, crate::Ownership)>,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src,
            pos: 0,
            regions: Vec::new(),
            region_map: HashMap::new(),
            memory: None,
            imports: Vec::new(),
            funcs: Vec::new(),
            ownership: Vec::new(),
        }
    }

    fn parse_module(mut self) -> Result<Module, String> {
        while self.pos < self.src.len() {
            self.skip_whitespace();
            if self.pos >= self.src.len() {
                break;
            }

            // Parse top-level declarations
            if self.peek_word("region") {
                self.parse_region()?;
            } else if self.peek_word("memory") {
                self.parse_memory()?;
            } else if self.peek_word("module") {
                // Module declaration - skip for now
                self.skip_declaration();
            } else if self.peek_word("fn") {
                self.parse_function()?;
            } else if self.peek_word("import") {
                self.parse_import()?;
            } else {
                // Skip comments and unknown declarations
                self.skip_declaration();
            }
        }

        Ok(Module {
            regions: self.regions,
            memory: self.memory,
            imports: self.imports,
            funcs: self.funcs,
            ownership: self.ownership,
        })
    }

    fn peek_word(&mut self, word: &str) -> bool {
        let start = self.pos;
        // Panic-safe: `get` returns None on an out-of-range / non-char-boundary
        // index instead of panicking on malformed or truncated input.
        if self.src.get(start..).is_some_and(|rest| rest.starts_with(word)) {
            let next_char = self.src.as_bytes().get(start + word.len());
            if next_char.is_none() || !next_char.unwrap().is_ascii_alphabetic() {
                return true;
            }
        }
        false
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            if c == b' ' || c == b'\t' || c == b'\n' || c == b'\r' {
                self.pos += 1;
            } else if c == b'/' {
                // Skip comments
                if self.pos + 1 < self.src.len() {
                    if self.src.as_bytes()[self.pos + 1] == b'/' {
                        // Single-line comment
                        self.pos += 2;
                        while self.pos < self.src.len() && self.src.as_bytes()[self.pos] != b'\n' {
                            self.pos += 1;
                        }
                    } else if self.src.as_bytes()[self.pos + 1] == b'*' {
                        // Block comment - skip for now (not common in current schemas)
                        self.pos += 2;
                        while self.pos < self.src.len() {
                            if self.pos + 1 < self.src.len() 
                                && self.src.as_bytes()[self.pos] == b'*' 
                                && self.src.as_bytes()[self.pos + 1] == b'/' {
                                self.pos += 2;
                                break;
                            }
                            self.pos += 1;
                        }
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }

    fn expect(&mut self, s: &str) -> Result<(), String> {
        self.skip_whitespace();
        if self.src.get(self.pos..).is_some_and(|rest| rest.starts_with(s)) {
            self.pos += s.len();
            Ok(())
        } else {
            // Panic-safe error context: clamp to the end of input and fall back
            // if the window straddles a UTF-8 boundary, so malformed/truncated
            // input yields an Err, never an out-of-bounds slice panic.
            let end = (self.pos + 20).min(self.src.len());
            let found = self.src.get(self.pos..end).unwrap_or("<end-of-input>");
            Err(format!(
                "Expected '{}' at position {}, found '{}'",
                s, self.pos, found
            ))
        }
    }

    fn parse_ident(&mut self) -> String {
        self.skip_whitespace();
        let start = self.pos;
        while self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            if c.is_ascii_alphanumeric() || c == b'_' {
                self.pos += 1;
            } else {
                break;
            }
        }
        self.src[start..self.pos].to_string()
    }

    fn parse_region(&mut self) -> Result<(), String> {
        self.expect("region")?;
        let name = self.parse_ident();
        self.skip_whitespace();

        // Parse optional array specifier: region Name[N]. We don't yet track
        // region cardinality, so the parsed size is discarded.
        if self.peek_char('[') {
            self.expect("[")?;
            let _n: u64 = self.parse_number()?;
            self.expect("]")?;
        }

        self.skip_whitespace();
        self.expect("{")?;

        let mut fields = Vec::new();
        let mut _align = 0u32;
        loop {
            self.skip_whitespace();
            if self.peek_char('}') {
                self.expect("}")?;
                break;
            }

            // Check for where clause
            if self.peek_word("where") {
                // Skip where clause: where <expr> ;
                self.expect("where")?;
                self.skip_whitespace();
                // Skip the expression - for now, just find the semicolon
                self.skip_to_semicolon();
                continue;
            }

            // Check for align clause
            if self.peek_word("align") {
                self.expect("align")?;
                self.skip_whitespace();
                let n: u64 = self.parse_number()?;
                _align = n as u32;
                self.skip_whitespace();
                // There might be a semicolon after align
                if self.peek_char(';') {
                    self.expect(";")?;
                }
                continue;
            }

            // Check for a constraint block: `invariant { ... }` (and similar
            // region-body annotation blocks). Skipped — the verifier checks
            // the schema/carriers, not these source-level constraints.
            if self.peek_word("invariant") {
                self.expect("invariant")?;
                self.skip_whitespace();
                self.expect("{")?;
                self.skip_to_brace_close();
                self.skip_whitespace();
                if self.peek_char(';') {
                    self.expect(";")?;
                }
                continue;
            }

            let field_name = self.parse_ident();
            self.skip_whitespace();
            self.expect(":")?;
            self.skip_whitespace();

            let (field_ty, field_cardinality) = self.parse_field_type()?;
            
            self.skip_whitespace();

            // Check for semicolon or comma
            if self.peek_char(';') {
                self.expect(";")?;
            } else if self.peek_char(',') {
                self.expect(",")?;
            }

            // For now, we don't track cardinality at the field level properly
            // The array cardinality is handled differently in the Rust IR
            fields.push(Field {
                name: field_name,
                ty: field_ty,
                cardinality: field_cardinality,
            });
        }

        // For now, we don't calculate byte_size - we'll need to compute it
        // based on field types. For the paint-type schemas, we can use
        // the hardcoded values.
        let byte_size = self.compute_region_byte_size(&fields)?;

        let region_index = self.regions.len();
        self.region_map.insert(name.clone(), region_index);
        self.regions.push(Region {
            name,
            fields,
            byte_size,
        });

        self.skip_whitespace();
        Ok(())
    }

    fn compute_region_byte_size(&self, fields: &[Field]) -> Result<u32, String> {
        let mut size = 0u32;
        for field in fields {
            let field_size = match field.ty {
                FieldTy::Scalar(s) => scalar_byte_size(&s),
                FieldTy::Ptr { .. } => 4, // Pointer is 4 bytes in wasm
            };
            // Checked arithmetic: a pathological schema (a field, or running
            // total, exceeding u32 bytes) is a parse error, never a panic.
            let contribution = field_size
                .checked_mul(field.cardinality)
                .ok_or_else(|| format!("field '{}' size overflows u32", field.name))?;
            size = size
                .checked_add(contribution)
                .ok_or_else(|| "region byte size overflows u32".to_string())?;
        }
        // Add padding if needed for alignment
        // For simplicity, we'll let the caller handle alignment
        Ok(size)
    }

    fn parse_field_type(&mut self) -> Result<(FieldTy, u32), String> {
        self.skip_whitespace();
        
        // Check for opt<T> nullable type
        let mut nullable = false;
        if self.peek_word("opt") {
            self.expect("opt")?;
            self.skip_whitespace();
            self.expect("<")?;
            nullable = true;
        }

        // Check for ptr<Region> / unique<Region> / ref<Region> field pointer
        // (e.g. `next: opt<ptr<FreeSlot>>`). Field-level region pointers, the
        // `@Region` form's keyword-with-angle-brackets sibling.
        if self.peek_word("ptr") || self.peek_word("unique") || self.peek_word("ref") {
            let kw = self.parse_ident();
            self.skip_whitespace();
            self.expect("<")?;
            self.skip_whitespace();
            let region_name = self.parse_ident();
            self.skip_whitespace();
            self.expect(">")?;
            if nullable {
                self.skip_whitespace();
                self.expect(">")?;
            }
            let kind = match kw.as_str() {
                "unique" => PtrKind::Exclusive,
                "ref" => PtrKind::Borrow,
                _ => PtrKind::Owning,
            };
            let target = self.region_map.get(&region_name).copied().unwrap_or(0);
            return Ok((FieldTy::Ptr { kind, target, nullable }, 1));
        }

        // Check for @Region reference
        if self.peek_char('@') {
            self.expect("@")?;
            let region_name = self.parse_ident();
            
            // Check for array: @Region[N] or @Region[expr]
            let cardinality: u32 = if self.peek_char('[') {
                self.expect("[")?;
                // Scan ahead to find the closing bracket and check for operators
                let start_bracket = self.pos;
                let mut found_op = false;
                let mut depth = 0;
                while self.pos < self.src.len() {
                    let c = self.src.as_bytes()[self.pos];
                    if c == b'[' {
                        depth += 1;
                    } else if c == b']' {
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                    } else if c == b'*' || c == b'+' || c == b'-' || c == b'/' {
                        found_op = true;
                    }
                    self.pos += 1;
                }
                
                // Reset and parse based on whether we found an operator
                self.pos = start_bracket;
                let n = if found_op {
                    self.parse_array_size_expr()?
                } else {
                    let n: u64 = self.parse_number()?;
                    n as u32
                };
                self.expect("]")?;
                n
            } else {
                1
            };

            // Check for closing > if we're inside opt<
            if nullable {
                self.skip_whitespace();
                self.expect(">")?;
            }
            
            // Look up the region index
            if let Some(&idx) = self.region_map.get(&region_name) {
                Ok((FieldTy::Ptr {
                    kind: PtrKind::Owning,
                    target: idx,
                    nullable,
                }, cardinality))
            } else {
                // Forward reference - will need to resolve later
                // For now, use index 0 as placeholder
                Ok((FieldTy::Ptr {
                    kind: PtrKind::Owning,
                    target: 0,
                    nullable,
                }, cardinality))
            }
        } else {
            // Parse scalar type with optional array
            let scalar = self.parse_scalar_type()?;
            let cardinality: u32 = if self.peek_char('[') {
                self.expect("[")?;
                // Parse array size - could be a number or an expression
                self.skip_whitespace();
                let n = if self.peek_char('*') || self.peek_char('+') || self.peek_char('-') || self.peek_char('/') {
                    // Expression - for now, evaluate simple expressions like "64 * 64"
                    self.parse_array_size_expr()?
                } else {
                    // Simple number
                    let n: u64 = self.parse_number()?;
                    n as u32
                };
                self.expect("]")?;
                n
            } else {
                1
            };
            // Check for closing > if we're inside opt<
            if nullable {
                self.skip_whitespace();
                self.expect(">")?;
            }
            Ok((FieldTy::Scalar(scalar), cardinality))
        }
    }

    fn parse_scalar_type(&mut self) -> Result<Scalar, String> {
        self.skip_whitespace();
        let ident = self.parse_ident();
        match ident.as_str() {
            "i8" => Ok(Scalar::I8),
            "i16" => Ok(Scalar::I16),
            "i32" => Ok(Scalar::I32),
            "i64" => Ok(Scalar::I64),
            "u8" => Ok(Scalar::U8),
            "u16" => Ok(Scalar::U16),
            "u32" => Ok(Scalar::U32),
            "u64" => Ok(Scalar::U64),
            "f32" => Ok(Scalar::F32),
            "f64" => Ok(Scalar::F64),
            "bool" => Ok(Scalar::Bool),
            _ => Err(format!("Unknown scalar type: {}", ident)),
        }
    }

    fn parse_number(&mut self) -> Result<u64, String> {
        self.skip_whitespace();
        let _start = self.pos;
        while self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            if c.is_ascii_digit() {
                self.pos += 1;
            } else {
                break;
            }
        }
        let s = self.src[_start..self.pos].to_string();
        s.parse::<u64>().map_err(|e| format!("Invalid number: {e}"))
    }

    /// Parse a simple array size expression like "64 * 64" or "1 + 2".
    /// For now, only handles binary expressions with two numeric operands.
    fn parse_array_size_expr(&mut self) -> Result<u32, String> {
        self.skip_whitespace();
        let left: u64 = self.parse_number()?;
        self.skip_whitespace();
        
        // Parse operator. Panic-safe index: truncated input after the left
        // operand yields an Err, never an out-of-bounds index panic.
        let Some(&op) = self.src.as_bytes().get(self.pos) else {
            return Err(
                "Expected operator in array size expression, found end of input".to_string(),
            );
        };
        if op != b'*' && op != b'+' && op != b'-' && op != b'/' {
            return Err(format!("Expected operator, found '{}'", op as char));
        }
        self.pos += 1;

        self.skip_whitespace();
        let right: u64 = self.parse_number()?;

        // Evaluate with checked arithmetic: a malformed expression (overflow,
        // division by zero, underflow) is a parse error, never a panic.
        let result: u64 = match op {
            b'*' => left
                .checked_mul(right)
                .ok_or_else(|| format!("array size expression overflows: {left} * {right}"))?,
            b'+' => left
                .checked_add(right)
                .ok_or_else(|| format!("array size expression overflows: {left} + {right}"))?,
            b'-' => left
                .checked_sub(right)
                .ok_or_else(|| format!("array size expression underflows: {left} - {right}"))?,
            b'/' => left
                .checked_div(right)
                .ok_or_else(|| format!("array size expression divides by zero: {left} / {right}"))?,
            _ => return Err(format!("Unknown operator: {}", op as char)),
        };

        u32::try_from(result).map_err(|_| format!("array size {result} does not fit in u32"))
    }

    fn peek_char(&mut self, c: char) -> bool {
        self.skip_whitespace();
        self.pos < self.src.len() && self.src.as_bytes()[self.pos] == c as u8
    }

    fn parse_memory(&mut self) -> Result<(), String> {
        self.expect("memory")?;
        let _name = self.parse_ident();
        self.skip_whitespace();
        self.expect("{")?;

        let mut initial = 1u64;
        let mut maximum = None;

        loop {
            self.skip_whitespace();
            if self.peek_char('}') {
                self.expect("}")?;
                break;
            }

            // Check for place directive
            if self.peek_word("place") {
                // place Region at offset;
                self.expect("place")?;
                let _region = self.parse_ident();
                self.skip_whitespace();
                self.expect("at")?;
                self.skip_whitespace();
                let _offset: u64 = self.parse_number()?;
                self.skip_whitespace();
                self.expect(";")?;
                continue;
            }

            let key = self.parse_ident();
            self.skip_whitespace();
            self.expect(":")?;
            self.skip_whitespace();

            let value: u64 = self.parse_number()?;
            self.skip_whitespace();

            match key.as_str() {
                "initial" => initial = value,
                "maximum" => maximum = Some(value),
                _ => {}
            }

            if self.peek_char(',') {
                self.expect(",")?;
            }
            
            // Skip semicolon if present
            if self.peek_char(';') {
                self.expect(";")?;
            }
        }

        self.memory = Some(Memory {
            min_pages: initial,
            max_pages: maximum,
        });

        Ok(())
    }

    #[allow(dead_code)]
    fn parse_module_decl(&mut self) -> Result<(), String> {
        self.expect("module")?;
        let _name = self.parse_ident();
        self.skip_whitespace();
        // Skip the rest of the module declaration
        while self.pos < self.src.len() && self.src.as_bytes()[self.pos] != b'{' {
            self.pos += 1;
        }
        if self.peek_char('{') {
            // Skip the body - we'll parse it as we go
            self.expect("{")?;
            // Don't consume the closing brace - let the main loop handle it
        }
        Ok(())
    }

    fn parse_function(&mut self) -> Result<(), String> {
        self.expect("fn")?;
        let name = self.parse_ident();
        self.skip_whitespace();

        self.expect("(")?;
        let mut params = Vec::new();
        // Per-param (name, region-index) for body lowering: a region-typed
        // param records the region it points at; scalar params record None.
        let mut param_meta: Vec<(String, Option<usize>)> = Vec::new();
        // L7/L10 ownership kinds per param (`own`/`&mut`/`&` qualifiers),
        // recorded into `Module::ownership` so the emitted module carries
        // the `typedwasm.ownership` section the verifier checks.
        let mut param_kinds: Vec<crate::Ownership> = Vec::new();
        loop {
            self.skip_whitespace();
            if self.peek_char(')') {
                self.expect(")")?;
                break;
            }

            // Parse optional parameter name. Params may be named (`p: &mut
            // region<T>`, `dt: f32`) or unnamed (`&mut region<Particles>`,
            // `i32`). Detect a `name:` prefix; if absent, rewind and parse the
            // type directly.
            let save = self.pos;
            let maybe_name = self.parse_ident();
            self.skip_whitespace();
            let pname = if !maybe_name.is_empty() && self.peek_char(':') {
                self.expect(":")?;
                self.skip_whitespace();
                maybe_name
            } else {
                self.pos = save;
                String::new()
            };

            // Parse the type, which may include ownership qualifiers
            let (param_ty, _, kind) = self.parse_param_type()?;

            // Map field type to Wty; remember the region a region-typed param
            // points at (for `region.get $p` lowering).
            let (wty, region) = match param_ty {
                FieldTy::Scalar(s) => (wty_from_scalar(&s), None),
                FieldTy::Ptr { target, .. } => (Wty::I32, Some(target)),
            };

            params.push(wty);
            param_meta.push((pname, region));
            param_kinds.push(kind);

            if self.peek_char(',') {
                self.expect(",")?;
            }
        }

        self.skip_whitespace();

        // Parse optional -> return type
        let mut results = Vec::new();
        let mut ret_kind = crate::Ownership::Unrestricted;
        if self.peek_word("->") {
            self.expect("->")?;
            self.skip_whitespace();

            // For now, assume single return type - parse it
            let (ret_ty, _, kind) = self.parse_param_type()?;
            ret_kind = kind;
            let wty = match ret_ty {
                FieldTy::Scalar(s) => wty_from_scalar(&s),
                FieldTy::Ptr { .. } => Wty::I32,
            };
            results.push(wty);
        }

        self.skip_whitespace();
        
        // Skip any annotation clauses before the body: `effects { ... }`,
        // `cost_bound { ... }`, `requires { ... }`, etc. The body is the
        // first `{` not preceded by an annotation keyword.
        loop {
            self.skip_whitespace();
            if self.peek_char('{') {
                break; // function body
            }
            let at = self.pos;
            if at < self.src.len() && (self.src.as_bytes()[at] as char).is_ascii_alphabetic() {
                let _annotation = self.parse_ident();
                self.skip_whitespace();
                if self.peek_char('{') {
                    self.expect("{")?;
                    self.skip_to_brace_close();
                    continue;
                }
            }
            break;
        }

        self.expect("{")?;

        // Step 1/2 body lowering: try to lower a simple field-reader (load) or
        // field-writer (store) body to real typed memory ops; fall back to a
        // representative stub otherwise. Each `try_lower_*` consumes through the
        // closing `}` on success; on a None it leaves the cursor unspecified, so
        // we restore `body_start` before the next attempt and before the stub.
        let body_start = self.pos;
        let lowered = self.try_lower_reader(&param_meta, &results).or_else(|| {
            self.pos = body_start;
            self.try_lower_writer(&params, &param_meta, &results)
        });
        let (body, accesses) = match lowered {
            Some((body, accesses)) => (body, accesses),
            None => {
                self.pos = body_start;
                let mut body = Vec::new();
                // Representative stub: drop all params, push a typed zero result.
                for i in 0..params.len() as u32 {
                    body.push(crate::Op::LocalGet(i));
                    body.push(crate::Op::Drop);
                }
                if let Some(&rty) = results.first() {
                    body.push(match rty {
                        Wty::I32 => crate::Op::I32Const(0),
                        Wty::I64 => crate::Op::I64Const(0),
                        Wty::F32 => crate::Op::F32Const(0.0),
                        Wty::F64 => crate::Op::F64Const(0.0),
                    });
                }
                self.skip_to_brace_close();
                (body, Vec::new())
            }
        };

        // Record the function's ownership signature when the source asked
        // for L7/L10 discipline anywhere in it. All-Unrestricted functions
        // stay out of the carrier (empty = no constraint, matching the
        // "empty = no L7/L10 carrier" Module contract).
        let has_discipline = ret_kind != crate::Ownership::Unrestricted
            || param_kinds
                .iter()
                .any(|k| *k != crate::Ownership::Unrestricted);
        if has_discipline {
            self.ownership.push((self.funcs.len(), param_kinds, ret_kind));
        }

        self.funcs.push(crate::Func {
            name,
            params,
            results,
            body,
            accesses,
            export: true, // All functions in .twasm are exported by default
        });

        Ok(())
    }

    /// Try to lower a single-statement field reader of the exact shape
    ///   region.get $p .field -> x ; return x ; }
    /// to a real typed load + access-site. Returns None (for the stub fallback)
    /// on any other body shape; the caller restores the cursor in that case.
    fn try_lower_reader(
        &mut self,
        param_meta: &[(String, Option<usize>)],
        results: &[Wty],
    ) -> Option<(Vec<crate::Op>, Vec<crate::AccessSite>)> {
        if !self.try_keyword("region") {
            return None;
        }
        if !self.try_char('.') {
            return None;
        }
        if !self.try_keyword("get") {
            return None;
        }
        if !self.try_char('$') {
            return None;
        }
        let pname = self.parse_ident();
        if !self.try_char('.') {
            return None;
        }
        let field = self.parse_ident();
        if !self.try_str("->") {
            return None;
        }
        let xname = self.parse_ident();
        if !self.try_char(';') {
            return None;
        }
        if !self.try_keyword("return") {
            return None;
        }
        self.try_char('$'); // optional `$` on the returned handle
        let retname = self.parse_ident();
        if !self.try_char(';') {
            return None;
        }
        if !self.try_char('}') {
            return None;
        }
        if retname != xname || pname.is_empty() || field.is_empty() {
            return None;
        }

        // Resolve the param to a region and the field to (index, offset, type).
        let p_idx = param_meta.iter().position(|(n, _)| n == &pname)?;
        let region = param_meta[p_idx].1?;
        let (field_idx, offset, scalar) = self.resolve_field(region, &field)?;
        let wty = wty_from_scalar(&scalar);
        if results.first() != Some(&wty) {
            return None; // result type must match the loaded field type
        }
        // Exact-width load (narrow fields sign/zero-extend, never over-read).
        let load = scalar_load_op(&scalar, offset as u64);

        // A load needs a memory to target; synthesise one big enough for the
        // accessed region if the module declared none (examples 02-06 don't).
        self.ensure_memory_for_region(region);

        let body = vec![crate::Op::LocalGet(p_idx as u32), load];
        let accesses = vec![crate::AccessSite {
            region,
            field: field_idx,
            // Body is [LocalGet, load]: the typed load is instruction index 1.
            instr_index: Some(1),
        }];
        Some((body, accesses))
    }

    /// Try to lower a single-statement field writer of the exact shape
    ///   region.set $p .field , <value> ; [return ;] }
    /// to a real typed store + access-site, where `<value>` is either a
    /// parameter of the matching wasm type or a numeric/bool literal. Returns
    /// None (for the stub fallback) on any other body shape — including a value
    /// that is a compound expression (`px + vx * dt`), which the trailing `;`
    /// guard rejects so it falls through to the stub. The caller restores the
    /// cursor on None.
    ///
    /// Stack order matches `example01::damage_player`: address (the region
    /// handle) is pushed first, then the value, then the store consumes both.
    fn try_lower_writer(
        &mut self,
        params: &[Wty],
        param_meta: &[(String, Option<usize>)],
        results: &[Wty],
    ) -> Option<(Vec<crate::Op>, Vec<crate::AccessSite>)> {
        // A setter returns nothing; a `-> T` here is some other shape.
        if !results.is_empty() {
            return None;
        }
        if !self.try_keyword("region") {
            return None;
        }
        if !self.try_char('.') {
            return None;
        }
        if !self.try_keyword("set") {
            return None;
        }
        if !self.try_char('$') {
            return None;
        }
        let pname = self.parse_ident();
        if !self.try_char('.') {
            return None;
        }
        let field = self.parse_ident();
        if !self.try_char(',') {
            return None;
        }

        // Resolve the destination first so we know the field's wasm type, which
        // the value must match.
        if pname.is_empty() || field.is_empty() {
            return None;
        }
        let p_idx = param_meta.iter().position(|(n, _)| n == &pname)?;
        let region = param_meta[p_idx].1?;
        let (field_idx, offset, scalar) = self.resolve_field(region, &field)?;
        let wty = wty_from_scalar(&scalar);

        // Parse the value to push: a matching-typed param, or a literal.
        let push = self.parse_store_value(params, param_meta, wty)?;

        if !self.try_char(';') {
            return None; // compound expr / extra statements -> stub
        }
        // An optional bare `return;` may close a setter.
        self.skip_whitespace();
        if self.try_keyword("return") && !self.try_char(';') {
            return None;
        }
        if !self.try_char('}') {
            return None;
        }

        // Exact-width store (narrow fields use store8/store16, never clobber).
        let store = scalar_store_op(&scalar, offset as u64);

        // A store needs a memory to target; synthesise one big enough for the
        // accessed region if the module declared none (examples 02-06 don't).
        self.ensure_memory_for_region(region);

        let body = vec![crate::Op::LocalGet(p_idx as u32), push, store];
        let accesses = vec![crate::AccessSite {
            region,
            field: field_idx,
            // Body is [LocalGet, push, store]: the typed store is index 2.
            instr_index: Some(2),
        }];
        Some((body, accesses))
    }

    /// Parse the right-hand side of a `region.set` as a single value op whose
    /// wasm type is `field_wty`: a parameter of that type (`local.get i`), a
    /// `true`/`false` (i32 0/1), or a numeric literal (typed const). Returns
    /// None on a type mismatch or a non-trivial expression, leaving the cursor
    /// for the caller to discard.
    fn parse_store_value(
        &mut self,
        params: &[Wty],
        param_meta: &[(String, Option<usize>)],
        field_wty: Wty,
    ) -> Option<crate::Op> {
        self.skip_whitespace();
        let &b = self.src.as_bytes().get(self.pos)?;

        // Numeric literal (optionally signed): float if it carries a '.',
        // otherwise an integer (decimal or `0x` hex bit pattern).
        if b == b'-' || b.is_ascii_digit() {
            return self.parse_numeric_store_value(field_wty);
        }

        // Identifier: a bool literal or a parameter name.
        let save = self.pos;
        let ident = self.parse_ident();
        match ident.as_str() {
            "true" if field_wty == Wty::I32 => return Some(crate::Op::I32Const(1)),
            "false" if field_wty == Wty::I32 => return Some(crate::Op::I32Const(0)),
            _ => {}
        }
        if let Some(i) = param_meta.iter().position(|(n, _)| n == &ident) {
            // The param must match the field's wasm type AND be a plain scalar,
            // not a region handle — both are i32 on the wasm stack, so without
            // the `.1.is_none()` guard a pointer would be laundered into a
            // scalar field. A handle-as-value falls through to the stub.
            if params.get(i) == Some(&field_wty) && param_meta[i].1.is_none() {
                return Some(crate::Op::LocalGet(i as u32));
            }
        }
        self.pos = save;
        None
    }

    /// Parse a lone numeric literal as a typed const matching `field_wty`.
    /// Decimal/hex integers map to I32/I64; a literal with a `.` maps to
    /// F32/F64. None on a kind/type mismatch.
    fn parse_numeric_store_value(&mut self, field_wty: Wty) -> Option<crate::Op> {
        self.skip_whitespace();
        let start = self.pos;
        if self.pos < self.src.len() && self.src.as_bytes()[self.pos] == b'-' {
            self.pos += 1;
        }
        let mut is_float = false;
        while self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            if c == b'.' {
                is_float = true;
                self.pos += 1;
            } else if c.is_ascii_alphanumeric() || c == b'_' {
                // covers digits, the `x` in `0x..`, and hex digits a-f
                self.pos += 1;
            } else {
                break;
            }
        }
        let tok = self.src.get(start..self.pos)?;
        if is_float {
            let v: f64 = tok.parse().ok()?;
            return match field_wty {
                Wty::F32 => {
                    // Reject a finite literal whose magnitude overflows f32 to
                    // ±inf — that would silently store a wrong value. Falls back
                    // to the stub rather than emitting `f32.const inf`.
                    let f = v as f32;
                    if f.is_infinite() && v.is_finite() {
                        None
                    } else {
                        Some(crate::Op::F32Const(f))
                    }
                }
                Wty::F64 => Some(crate::Op::F64Const(v)),
                _ => None,
            };
        }
        // Integer: parse the bit pattern, allowing `0x` hex.
        let value: i64 = if let Some(hex) = tok.strip_prefix("0x").or_else(|| tok.strip_prefix("0X")) {
            u64::from_str_radix(hex, 16).ok()? as i64
        } else {
            tok.parse::<i64>().ok()?
        };
        match field_wty {
            // Accept the full signed-or-unsigned 32-bit range; reject anything
            // wider (e.g. 4294967296, 0x1FFFFFFFF) rather than silently wrapping
            // via `as i32`. Out-of-range literals fall back to the stub.
            Wty::I32 => i32::try_from(value)
                .or_else(|_| u32::try_from(value).map(|u| u as i32))
                .ok()
                .map(crate::Op::I32Const),
            Wty::I64 => Some(crate::Op::I64Const(value)),
            _ => None,
        }
    }

    /// Ensure a linear memory exists that covers the given region's bytes, so a
    /// synthesised store/load offset (the field's byte-offset, < region size)
    /// cannot point past the declared memory and trap at runtime. Only fills in
    /// a memory when the module declared none; a declared memory is the author's.
    fn ensure_memory_for_region(&mut self, region: usize) {
        if self.memory.is_none() {
            let bytes = self.regions.get(region).map_or(0, |r| r.byte_size as u64);
            self.memory = Some(Memory {
                min_pages: bytes.div_ceil(65536).max(1),
                max_pages: None,
            });
        }
    }

    /// Resolve a field name within a region to (field index, byte offset,
    /// scalar type). None for unknown or non-scalar (pointer) fields.
    fn resolve_field(&self, region_idx: usize, field_name: &str) -> Option<(usize, u32, Scalar)> {
        let region = self.regions.get(region_idx)?;
        let mut offset = 0u32;
        for (i, f) in region.fields.iter().enumerate() {
            if f.name == field_name {
                return match f.ty {
                    FieldTy::Scalar(s) => Some((i, offset, s)),
                    FieldTy::Ptr { .. } => None,
                };
            }
            let size = match f.ty {
                FieldTy::Scalar(s) => scalar_byte_size(&s),
                FieldTy::Ptr { .. } => 4,
            };
            // Checked: a region whose fields overrun u32 cannot yield a sane
            // offset, so treat it as unresolvable (caller falls back to the
            // stub) rather than panicking on overflow.
            offset = offset.checked_add(size.checked_mul(f.cardinality)?)?;
        }
        None
    }

    /// Non-erroring: consume `c` if present at the cursor (skips leading ws).
    fn try_char(&mut self, c: char) -> bool {
        self.skip_whitespace();
        if self.pos < self.src.len() && self.src.as_bytes()[self.pos] == c as u8 {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Non-erroring: consume whole keyword `kw` if present.
    fn try_keyword(&mut self, kw: &str) -> bool {
        self.skip_whitespace();
        if self.peek_word(kw) {
            self.pos += kw.len();
            true
        } else {
            false
        }
    }

    /// Non-erroring: consume literal `s` if present.
    fn try_str(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        if self.src.get(self.pos..).is_some_and(|r| r.starts_with(s)) {
            self.pos += s.len();
            true
        } else {
            false
        }
    }

    /// Parse a parameter type which may include ownership qualifiers like 'own', '&', '&mut'.
    /// The third component is the L7/L10 ownership kind the qualifier denotes:
    /// `own` → Linear, `&mut` → ExclBorrow, `&` → SharedBorrow. A bare
    /// `region<T>` (no qualifier) and every scalar stay Unrestricted — the
    /// carrier only asserts discipline the source explicitly asked for.
    fn parse_param_type(&mut self) -> Result<(FieldTy, u32, crate::Ownership), String> {
        self.skip_whitespace();
        
        // Check for ownership qualifier
        let mut is_own = false;
        let mut is_excl_borrow = false;
        let mut is_shared_borrow = false;
        
        if self.peek_word("own") {
            self.expect("own")?;
            is_own = true;
            self.skip_whitespace();
        } else if self.peek_word("&mut") {
            self.expect("&")?;
            self.expect("mut")?;
            is_excl_borrow = true;
            self.skip_whitespace();
        } else if self.peek_char('&') {
            self.expect("&")?;
            is_shared_borrow = true;
            self.skip_whitespace();
        }
        
        // Now parse the actual type
        self.skip_whitespace();
        
        // Check for region<T> syntax
        if self.peek_word("region") {
            self.expect("region")?;
            self.skip_whitespace();
            self.expect("<")?;
            let region_name = self.parse_ident();
            self.expect(">")?;
            
            // Look up the region index
            let idx = self.region_map.get(&region_name)
                .copied()
                .unwrap_or(0);
            
            let kind = if is_own {
                PtrKind::Owning
            } else if is_excl_borrow {
                PtrKind::Exclusive
            } else if is_shared_borrow {
                PtrKind::Borrow
            } else {
                PtrKind::Owning // default
            };
            
            let ownership = if is_own {
                crate::Ownership::Linear
            } else if is_excl_borrow {
                crate::Ownership::ExclBorrow
            } else if is_shared_borrow {
                crate::Ownership::SharedBorrow
            } else {
                crate::Ownership::Unrestricted
            };
            Ok((FieldTy::Ptr {
                kind,
                target: idx,
                nullable: false,
            }, 1, ownership))
        } else {
            // Parse as normal field type
            let (ty, card) = self.parse_field_type()?;
            Ok((ty, card, crate::Ownership::Unrestricted))
        }
    }

    /// Skip to closing brace, handling nested braces
    fn skip_to_brace_close(&mut self) {
        let mut depth = 1;
        while self.pos < self.src.len() && depth > 0 {
            let c = self.src.as_bytes()[self.pos];
            if c == b'{' {
                depth += 1;
            } else if c == b'}' {
                depth -= 1;
            }
            self.pos += 1;
        }
    }

    #[allow(dead_code)]
    fn parse_region_op(&mut self, body: &mut Vec<crate::Op>, _accesses: &mut Vec<crate::AccessSite>) -> Result<(), String> {
        self.expect("region")?;
        self.skip_whitespace();
        
        if self.peek_word("alloc") {
            self.expect("alloc")?;
            // region.alloc Region { ... } -> handle
            // For now, just emit a placeholder
            body.push(crate::Op::I32Const(0));
        } else if self.peek_word("free") {
            self.expect("free")?;
            body.push(crate::Op::Drop);
        } else if self.peek_word("scan") {
            self.expect("scan")?;
            body.push(crate::Op::LocalGet(0));
            body.push(crate::Op::Drop);
        } else if self.peek_word("get") {
            self.expect("get")?;
            body.push(crate::Op::LocalGet(0));
            body.push(crate::Op::Drop);
        } else if self.peek_word("set") {
            self.expect("set")?;
            body.push(crate::Op::LocalGet(0));
            body.push(crate::Op::Drop);
        } else if self.peek_word("place") {
            self.expect("place")?;
            // region.place Region at offset
            // Skip for now
        }
        
        Ok(())
    }

    fn skip_to_semicolon(&mut self) {
        while self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            if c == b';' {
                self.pos += 1;
                return;
            } else if c == b'{' {
                // Skip nested block
                self.pos += 1;
                let mut depth = 1;
                while self.pos < self.src.len() && depth > 0 {
                    let c = self.src.as_bytes()[self.pos];
                    if c == b'{' {
                        depth += 1;
                    } else if c == b'}' {
                        depth -= 1;
                    }
                    self.pos += 1;
                }
            } else {
                self.pos += 1;
            }
        }
    }

    fn skip_declaration(&mut self) {
        while self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            if c == b';' {
                self.pos += 1;
                return;
            } else if c == b'{' {
                self.pos += 1;
                let mut depth = 1;
                while self.pos < self.src.len() && depth > 0 {
                    let c = self.src.as_bytes()[self.pos];
                    if c == b'{' {
                        depth += 1;
                    } else if c == b'}' {
                        depth -= 1;
                    }
                    self.pos += 1;
                }
            } else {
                self.pos += 1;
            }
        }
    }

    fn parse_import(&mut self) -> Result<(), String> {
        self.expect("import")?;
        self.skip_whitespace();
        // Optional `region` keyword: `import region Name from "module" ...`
        if self.peek_word("region") {
            self.expect("region")?;
            self.skip_whitespace();
        }
        let _name = self.parse_ident();
        self.skip_whitespace();
        self.expect("from")?;
        self.skip_whitespace();
        // Module source: a quoted string ("game_server") or a bare ident.
        if self.peek_char('"') {
            self.expect("\"")?;
            while self.pos < self.src.len() && self.src.as_bytes()[self.pos] != b'"' {
                self.pos += 1;
            }
            self.expect("\"")?;
        } else {
            let _module = self.parse_ident();
        }
        self.skip_whitespace();
        // Either a re-declaration body `{ ... }` (multi-module) or a `;`.
        if self.peek_char('{') {
            self.expect("{")?;
            self.skip_to_brace_close();
        } else if self.peek_char(';') {
            self.expect(";")?;
        }
        Ok(())
    }
}

fn scalar_byte_size(s: &Scalar) -> u32 {
    match s {
        Scalar::I8 | Scalar::U8 => 1,
        Scalar::I16 | Scalar::U16 => 2,
        Scalar::I32 | Scalar::U32 | Scalar::F32 => 4,
        Scalar::I64 | Scalar::U64 | Scalar::F64 => 8,
        Scalar::Bool => 1, // bool is typically 1 byte
    }
}

fn wty_from_scalar(s: &Scalar) -> Wty {
    match s {
        Scalar::I32 | Scalar::U32 => Wty::I32,
        Scalar::I64 | Scalar::U64 => Wty::I64,
        Scalar::F32 => Wty::F32,
        Scalar::F64 => Wty::F64,
        _ => Wty::I32, // Default for i8, i16, u8, u16, bool
    }
}

/// The exact-width load op for a scalar field at `offset`. Narrow integers use
/// sub-width loads (sign-extending for signed, zero-extending for unsigned/bool)
/// so a 1- or 2-byte field reads exactly its own bytes — never the neighbour's.
fn scalar_load_op(s: &Scalar, offset: u64) -> crate::Op {
    use crate::Op::*;
    match s {
        Scalar::I8 => I32Load8S { offset },
        Scalar::U8 | Scalar::Bool => I32Load8U { offset },
        Scalar::I16 => I32Load16S { offset },
        Scalar::U16 => I32Load16U { offset },
        Scalar::I32 | Scalar::U32 => I32Load { offset },
        Scalar::I64 | Scalar::U64 => I64Load { offset },
        Scalar::F32 => F32Load { offset },
        Scalar::F64 => F64Load { offset },
    }
}

/// The exact-width store op for a scalar field at `offset`. Narrow integers use
/// store8/store16, writing only the field's own bytes (no clobber of the
/// adjacent field, no over-run past the region).
fn scalar_store_op(s: &Scalar, offset: u64) -> crate::Op {
    use crate::Op::*;
    match s {
        Scalar::I8 | Scalar::U8 | Scalar::Bool => I32Store8 { offset },
        Scalar::I16 | Scalar::U16 => I32Store16 { offset },
        Scalar::I32 | Scalar::U32 => I32Store { offset },
        Scalar::I64 | Scalar::U64 => I64Store { offset },
        Scalar::F32 => F32Store { offset },
        Scalar::F64 => F64Store { offset },
    }
}

#[cfg(test)]
mod totality_tests {
    use super::*;

    // T3 — parser totality: the three previously-panicking arithmetic sites
    // (array-size expression, region byte size, field offset) now degrade to
    // an error / `None` on malformed or pathological input, never a panic.
    // Each negative test is paired with a well-formed control so it is the
    // fault being rejected, not the path being broken.

    #[test]
    fn array_size_div_by_zero_is_err_not_panic() {
        let mut p = Parser::new("4 / 0");
        assert!(p.parse_array_size_expr().is_err());
    }

    #[test]
    fn array_size_overflow_is_err_not_panic() {
        // 1e10 * 1e10 = 1e20 overflows u64 -> checked_mul None -> Err.
        let mut p = Parser::new("10000000000 * 10000000000");
        assert!(p.parse_array_size_expr().is_err());
    }

    #[test]
    fn array_size_u32_overflow_is_err_not_panic() {
        // Fits in u64 but not u32 -> try_from Err, not a silent truncation.
        let mut p = Parser::new("100000 * 100000");
        assert!(p.parse_array_size_expr().is_err());
    }

    #[test]
    fn array_size_underflow_is_err_not_panic() {
        let mut p = Parser::new("1 - 2");
        assert!(p.parse_array_size_expr().is_err());
    }

    #[test]
    fn array_size_truncated_after_operand_is_err_not_panic() {
        // No operator byte after the operand: was an out-of-bounds index panic.
        let mut p = Parser::new("5");
        assert!(p.parse_array_size_expr().is_err());
    }

    #[test]
    fn array_size_well_formed_still_evaluates() {
        let mut p = Parser::new("64 * 64");
        assert_eq!(p.parse_array_size_expr(), Ok(4096));
    }

    #[test]
    fn region_byte_size_overflow_is_err_not_panic() {
        let p = Parser::new("");
        let fields = vec![
            Field::array("a", Scalar::U8, 3_000_000_000),
            Field::array("b", Scalar::U8, 3_000_000_000), // sum 6e9 > u32::MAX
        ];
        assert!(p.compute_region_byte_size(&fields).is_err());
    }

    #[test]
    fn region_byte_size_normal_is_ok() {
        let p = Parser::new("");
        let fields = vec![Field::scalar("a", Scalar::I32), Field::scalar("b", Scalar::U8)];
        assert_eq!(p.compute_region_byte_size(&fields), Ok(5));
    }

    #[test]
    fn resolve_field_offset_overflow_is_none_not_panic() {
        let mut p = Parser::new("");
        p.regions.push(Region {
            name: "R".into(),
            fields: vec![
                Field::array("pad", Scalar::U8, 4_000_000_000),
                Field::array("pad2", Scalar::U8, 4_000_000_000), // offset 8e9 > u32::MAX
                Field::scalar("target", Scalar::I32),
            ],
            byte_size: 0,
        });
        assert!(p.resolve_field(0, "target").is_none());
    }

    #[test]
    fn resolve_field_normal_offsets_resolve() {
        let mut p = Parser::new("");
        p.regions.push(Region {
            name: "R".into(),
            fields: vec![Field::scalar("a", Scalar::I32), Field::scalar("b", Scalar::U8)],
            byte_size: 5,
        });
        // 'b' sits at offset 4 (after the i32).
        assert!(matches!(p.resolve_field(0, "b"), Some((1, 4, Scalar::U8))));
    }
}
