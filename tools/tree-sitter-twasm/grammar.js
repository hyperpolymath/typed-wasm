// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// tree-sitter grammar for typed-wasm (.twasm).
//
// SCOPE (v1, Phase 0 grammar extension): full coverage of
// examples/01-single-module.twasm. That means region declarations,
// memory declarations, function declarations with parameters / effects
// / return types, and the statement and expression forms used in
// example 01 — region.get / region.set / region.scan / let / return /
// if / binary operators / is_null / field paths.
//
// STILL DEFERRED (next Track A PR):
//   - Imports/exports (import region X from "mod"; export region X;)
//   - Invariant declarations and proof statements
//   - Const declarations
//   - Block-expression if (`yield`)
//   - Match on union regions
//   - L13–L16 surface (isolated, session, capability, choreography)
//   - L11/L12 surface (cost_bound, fresh, version_of, region.sync)
//   - Lifetime annotations on function decls
//   - Striated region layout
//
// The deferrals are sequenced for the next Track A PR; the v1 here
// closes the gap between scaffold (region-decls only) and "can parse
// the simplest end-to-end example".

module.exports = grammar({
  name: 'twasm',

  extras: $ => [
    /\s+/,
    $.line_comment,
  ],

  word: $ => $.identifier,

  precedences: $ => [
    ['unary', 'mul', 'add', 'cmp', 'and', 'or'],
  ],

  rules: {
    // ---- Top-level ----

    source_file: $ => repeat($._declaration),

    _declaration: $ => choice(
      $.region_decl,
      $.memory_decl,
      $.function_decl,
    ),

    // ---- Region declarations ----

    region_decl: $ => seq(
      'region',
      field('name', $.identifier),
      optional($.region_quantifier),
      '{',
      repeat(choice($.field_decl, $.where_constraint)),
      optional($.align_clause),
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

    where_constraint: $ => seq(
      'where',
      $._integer,
      $._range_op,
      $.identifier,
      $._range_op,
      $._integer,
      ';',
    ),

    _range_op: $ => choice('<=', '<', '>=', '>'),

    // ---- Memory declarations ----

    memory_decl: $ => seq(
      'memory',
      field('name', $.identifier),
      '{',
      $.initial_clause,
      optional($.maximum_clause),
      repeat($.place_clause),
      '}',
    ),

    initial_clause: $ => seq('initial', ':', $._integer, ';'),
    maximum_clause: $ => seq('maximum', ':', $._integer, ';'),
    place_clause: $ => seq('place', $.identifier, 'at', $._integer, ';'),

    // ---- Function declarations ----

    function_decl: $ => seq(
      'fn',
      field('name', $.identifier),
      '(',
      optional($.parameter_list),
      ')',
      optional($.return_type),
      optional($.effects_clause),
      '{',
      repeat($._statement),
      '}',
    ),

    parameter_list: $ => seq(
      $.parameter,
      repeat(seq(',', $.parameter)),
      optional(','),
    ),

    parameter: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $._param_type),
    ),

    _param_type: $ => choice(
      $._field_type,
      $.region_handle_type,
    ),

    region_handle_type: $ => seq(
      $.handle_mode,
      'region',
      '<',
      $.identifier,
      '>',
    ),

    handle_mode: $ => choice('&mut', '&', 'own'),

    return_type: $ => seq('->', choice($._field_type, 'void')),

    effects_clause: $ => seq(
      'effects',
      '{',
      $.effect,
      repeat(seq(',', $.effect)),
      '}',
    ),

    effect: $ => choice(
      'Read', 'Write', 'Alloc', 'Free',
      seq('ReadRegion', '(', $.identifier, ')'),
      seq('WriteRegion', '(', $.identifier, ')'),
    ),

    // ---- Statements ----

    _statement: $ => choice(
      $.region_get_stmt,
      $.region_set_stmt,
      $.region_scan_stmt,
      $.let_stmt,
      $.assign_stmt,
      $.if_stmt,
      $.return_stmt,
    ),

    region_get_stmt: $ => seq(
      'region.get',
      $.region_target,
      $.field_path,
      '->',
      field('binding', $.identifier),
      ';',
    ),

    region_set_stmt: $ => seq(
      'region.set',
      $.region_target,
      $.field_path,
      ',',
      $._expression,
      ';',
    ),

    region_scan_stmt: $ => seq(
      'region.scan',
      $.region_target,
      optional(seq('where', $._expression)),
      '->',
      '|',
      field('binding', $.identifier),
      '|',
      '{',
      repeat($._statement),
      '}',
    ),

    region_target: $ => choice(
      seq('$', $.identifier),
      seq('$', $.identifier, '[', $._expression, ']'),
      // bare identifier — for post-null-check bound refs like maybe_target
      $.identifier,
    ),

    field_path: $ => seq(
      '.',
      $.identifier,
      repeat(seq('.', $.identifier)),
    ),

    let_stmt: $ => seq(
      'let',
      optional('mut'),
      field('name', $.identifier),
      optional(seq(':', $._field_type)),
      '=',
      $._expression,
      ';',
    ),

    // Assignment (used in scan bodies: count = count + 1;)
    assign_stmt: $ => seq(
      $.identifier,
      '=',
      $._expression,
      ';',
    ),

    if_stmt: $ => seq(
      'if',
      $._expression,
      '{',
      repeat($._statement),
      '}',
      optional(seq(
        'else',
        '{',
        repeat($._statement),
        '}',
      )),
    ),

    return_stmt: $ => seq('return', optional($._expression), ';'),

    // ---- Expressions ----

    _expression: $ => choice(
      $.literal,
      $.identifier_expr,
      $.region_var,
      $.binary_expr,
      $.unary_expr,
      $.is_null_expr,
      $.paren_expr,
    ),

    identifier_expr: $ => $.identifier,
    region_var: $ => seq('$', $.identifier),

    binary_expr: $ => choice(
      prec.left('mul', seq($._expression, choice('*', '/', '%'), $._expression)),
      prec.left('add', seq($._expression, choice('+', '-'), $._expression)),
      prec.left('cmp', seq($._expression, choice('==', '!=', '<', '>', '<=', '>='), $._expression)),
      prec.left('and', seq($._expression, '&&', $._expression)),
      prec.left('or',  seq($._expression, '||', $._expression)),
    ),

    unary_expr: $ => prec.right('unary', seq(choice('-', '!'), $._expression)),

    is_null_expr: $ => seq('is_null', '(', $._expression, ')'),

    paren_expr: $ => seq('(', $._expression, ')'),

    literal: $ => choice(
      $.integer_literal,
      $.float_literal,
      'true',
      'false',
      'null',
    ),

    // ---- Lexical ----

    identifier: $ => /[A-Za-z_][A-Za-z0-9_]*/,

    integer_literal: $ => /-?[0-9]+/,
    float_literal: $ => /-?[0-9]+\.[0-9]+/,

    _integer: $ => /[0-9]+/,

    line_comment: $ => token(seq('//', /[^\n]*/)),
  },
});
