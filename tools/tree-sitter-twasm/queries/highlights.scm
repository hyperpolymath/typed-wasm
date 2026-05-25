; SPDX-License-Identifier: MPL-2.0
; Tree-sitter syntax-highlight queries for typed-wasm (.twasm).
;
; v1 — covers regions + memory + functions + statements scope.

; Keywords — declarations
"region" @keyword
"memory" @keyword
"fn"     @keyword
"opt"    @keyword
"align"  @keyword
"where"  @keyword

; Keywords — function clauses
"effects" @keyword
"return"  @keyword.return

; Keywords — statements
"let"        @keyword
"mut"        @keyword
"if"         @keyword.conditional
"else"       @keyword.conditional
"region.get" @keyword
"region.set" @keyword
"region.scan" @keyword

; Keywords — memory directives
"initial" @property
"maximum" @property
"place"   @keyword
"at"      @keyword

; Built-in effects
"Read"        @type.builtin
"Write"       @type.builtin
"Alloc"       @type.builtin
"Free"        @type.builtin
"ReadRegion"  @function.builtin
"WriteRegion" @function.builtin
"is_null"     @function.builtin

; Types
(primitive_type) @type.builtin
(region_ref (identifier) @type)

; Definitions
(region_decl    name: (identifier) @type.definition)
(memory_decl    name: (identifier) @type.definition)
(function_decl  name: (identifier) @function)
(field_decl     name: (identifier) @property)
(parameter      name: (identifier) @variable.parameter)
(let_stmt       name: (identifier) @variable)

; Handle modes
(handle_mode)   @keyword.modifier

; Literals
(integer_literal) @number
(float_literal)   @number.float
"true"  @boolean
"false" @boolean
"null"  @constant.builtin

; Comments
(line_comment) @comment

