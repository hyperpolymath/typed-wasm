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
    ownership: Vec<(usize, Vec<crate::Ownership>)>,
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
        if self.src[start..].starts_with(word) {
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
        if self.src[self.pos..].starts_with(s) {
            self.pos += s.len();
            Ok(())
        } else {
            Err(format!(
                "Expected '{}' at position {}, found '{}'",
                s,
                self.pos,
                &self.src[self.pos..self.pos + 20]
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

        // Parse optional array specifier: region Name[N]
        let _cardinality = if self.peek_char('[') {
            self.expect("[")?;
            let _n: u64 = self.parse_number()?;
            self.expect("]")?;
            // For now, we don't handle region arrays properly
        };

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
        let byte_size = self.compute_region_byte_size(&fields);

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

    fn compute_region_byte_size(&self, fields: &[Field]) -> u32 {
        let mut size = 0u32;
        for field in fields {
            let field_size = match field.ty {
                FieldTy::Scalar(s) => scalar_byte_size(&s),
                FieldTy::Ptr { .. } => 4, // Pointer is 4 bytes in wasm
            };
            size += field_size * field.cardinality;
        }
        // Add padding if needed for alignment
        // For simplicity, we'll let the caller handle alignment
        size
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
        
        // Parse operator
        let op = self.src.as_bytes()[self.pos];
        if op != b'*' && op != b'+' && op != b'-' && op != b'/' {
            return Err(format!("Expected operator, found '{}'", op as char));
        }
        self.pos += 1;
        
        self.skip_whitespace();
        let right: u64 = self.parse_number()?;
        
        // Evaluate the expression
        let result = match op {
            b'*' => left * right,
            b'+' => left + right,
            b'-' => left - right,
            b'/' => left / right,
            _ => return Err(format!("Unknown operator: {}", op as char)),
        };
        
        Ok(result as u32)
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
        loop {
            self.skip_whitespace();
            if self.peek_char(')') {
                self.expect(")")?;
                break;
            }

            // Parse parameter: name: type (skip name, just get type)
            let _param_name = self.parse_ident();
            self.skip_whitespace();
            self.expect(":")?;
            self.skip_whitespace();

            // Parse the type, which may include ownership qualifiers
            let (param_ty, _) = self.parse_param_type()?;
            
            // Map field type to Wty for parameters
            let wty = match param_ty {
                FieldTy::Scalar(s) => wty_from_scalar(&s),
                FieldTy::Ptr { .. } => Wty::I32, // Pointers are passed as i32 indices
            };

            params.push(wty);

            if self.peek_char(',') {
                self.expect(",")?;
            }
        }

        self.skip_whitespace();

        // Parse optional -> return type
        let mut results = Vec::new();
        if self.peek_word("->") {
            self.expect("->")?;
            self.skip_whitespace();
            
            // For now, assume single return type - parse it
            let (ret_ty, _) = self.parse_param_type()?;
            let wty = match ret_ty {
                FieldTy::Scalar(s) => wty_from_scalar(&s),
                FieldTy::Ptr { .. } => Wty::I32,
            };
            results.push(wty);
        }

        self.skip_whitespace();
        
        // Skip effects annotation if present: effects { ... }
        if self.peek_word("effects") {
            self.expect("effects")?;
            self.skip_whitespace();
            self.expect("{")?;
            self.skip_to_brace_close();
        }
        
        self.expect("{")?;

        // Parse function body and emit placeholder ops
        // For v0, we emit: drop all params, then i32.const 0 if there are results
        let mut body = Vec::new();
        
        // Emit placeholder: drop all parameters
        for i in 0..params.len() as u32 {
            body.push(crate::Op::LocalGet(i));
            body.push(crate::Op::Drop);
        }
        
        // If function returns a value, emit a constant 0
        if !results.is_empty() {
            // For now, assume i32 result
            body.push(crate::Op::I32Const(0));
        }
        
        let accesses = Vec::new();
        
        // Skip the actual function body in the source
        self.skip_to_brace_close();

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

    /// Parse a parameter type which may include ownership qualifiers like 'own', '&', '&mut'
    fn parse_param_type(&mut self) -> Result<(FieldTy, u32), String> {
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
            
            Ok((FieldTy::Ptr {
                kind,
                target: idx,
                nullable: false,
            }, 1))
        } else {
            // Parse as normal field type
            self.parse_field_type()
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
        let _name = self.parse_ident();
        self.skip_whitespace();
        self.expect("from")?;
        self.skip_whitespace();
        let _module = self.parse_ident();
        self.skip_whitespace();
        self.expect(";")?;
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
