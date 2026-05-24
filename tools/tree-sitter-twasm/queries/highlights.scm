; SPDX-License-Identifier: MPL-2.0
; Tree-sitter syntax-highlight queries for typed-wasm (.twasm).
;
; Minimal v0 — covers region-decl scope only. Will grow alongside grammar.js.

"region" @keyword
"opt"    @keyword
"align"  @keyword
"where"  @keyword

(primitive_type) @type
(region_ref (identifier) @type)

(region_decl name: (identifier) @type.definition)
(field_decl  name: (identifier) @property)

(line_comment) @comment
