// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// tree-sitter grammar for typed-wasm (.twasm).
//
// SCOPE (v0 scaffold, Phase 0): region declarations only.
//   - region Name { field: type; ... }
//   - region Name[N] { ... } with array quantifier
//   - primitive field types, region refs (@T), opt<T>, fixed arrays (u8[24])
//   - align clauses, where constraints
//   - // line comments
//
// EVERYTHING ELSE (functions, statements, imports/exports, memory decls,
// L11-L16 surface) is NOT yet covered. Extending to full spec/grammar.ebnf
// parity is the second deliverable of Track A; see the package README for
// the staged plan.

module.exports = grammar({
  name: 'twasm',

  extras: $ => [
    /\s+/,
    $.line_comment,
  ],

  rules: {
    // ---- Top-level ----

    source_file: $ => repeat($._declaration),

    _declaration: $ => choice(
      $.region_decl,
      // TODO Phase 0/1: import_region_decl, export_region_decl,
      //                 function_decl, memory_decl, invariant_decl,
      //                 const_decl, L13-L16 forms.
    ),

    // ---- Region declarations (the v0 coverage) ----

    region_decl: $ => seq(
      'region',
      field('name', $.identifier),
      optional($.region_quantifier),
      '{',
      repeat($.field_decl),
      optional($.align_clause),
      optional($.where_block),
      '}',
    ),

    region_quantifier: $ => seq('[', $._integer, ']'),

    field_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $._field_type),
      ';',
    ),

    _field_type: $ => choice(
      $.primitive_type,
      $.region_ref,
      $.optional_type,
      $.array_field_type,
    ),

    primitive_type: $ => choice(
      'i8', 'i16', 'i32', 'i64',
      'u8', 'u16', 'u32', 'u64',
      'f32', 'f64',
      'bool',
    ),

    region_ref: $ => seq('@', $.identifier),

    optional_type: $ => seq('opt', '<', $._field_type, '>'),

    array_field_type: $ => seq(
      $._field_type_no_array,
      '[',
      $._integer,
      ']',
    ),

    _field_type_no_array: $ => choice(
      $.primitive_type,
      $.region_ref,
      $.optional_type,
    ),

    align_clause: $ => seq('align', $._integer, ';'),

    // v0 supports the range form only:
    //   where LO <= field <= HI ;
    where_block: $ => seq(
      'where',
      $._range_constraint,
      repeat(seq(',', $._range_constraint)),
      ';',
    ),

    _range_constraint: $ => seq(
      $._integer,
      $._range_op,
      $.identifier,
      $._range_op,
      $._integer,
    ),

    _range_op: $ => choice('<=', '<', '>=', '>'),

    // ---- Lexical ----

    identifier: $ => /[A-Za-z_][A-Za-z0-9_]*/,

    _integer: $ => /[0-9]+/,

    line_comment: $ => token(seq('//', /[^\n]*/)),
  },
});
