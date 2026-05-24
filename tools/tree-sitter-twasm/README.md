# tree-sitter-twasm

Tree-sitter grammar for `.twasm` (typed-wasm surface syntax).

## Status: scaffold (Phase 0 kickoff)

This is the **scaffold** for the tree-sitter grammar that will eventually
back the Idris2 parser, the LSP, Linguist registration, and editor
plugins. See `docs/PRODUCTION-PATH.adoc` §Phase 0 for the strategic
context.

### What works today

- Tree-sitter scaffold + corpus harness (`tree-sitter test` runs)
- `grammar.js` v0 — covers **region declarations only**:
  - `region Name { field: type; ... }`
  - `region Name[N] { ... }` (array quantifier)
  - Primitive types (`i32`, `f32`, `u8`, `bool`, etc.)
  - Nested region references (`@OtherRegion`)
  - Optional types (`opt<@T>`)
  - Fixed-size array fields (`u8[24]`)
  - `align N;` clauses
  - `where` field constraints (range form)
  - Single-line `//` comments

### What does NOT work yet (deferred to subsequent Track A PRs)

- Function declarations (`fn name(...) { ... }`)
- Memory declarations, imports/exports
- Statements: `region.get`, `region.set`, `let`, `if`, `while`
- Effects, lifetime, cost-bound, freshness clauses
- L13–L16 surface syntax (isolated modules, sessions, capabilities, choreography)
- Tropical / epistemic extensions (L11/L12)
- The full v1.5 surface — see `spec/grammar.ebnf` (~695 lines) for what's still ahead

This deliberate v0 scope covers enough of `examples/01-single-module.twasm`
to exercise the toolchain end-to-end without overcommitting to the
multi-month full-grammar port.

## Why in-tree first

Production-path Phase 0 §Track A specifies "in-tree at
`tools/tree-sitter-twasm/`, extract later". Rationale: changes to
`spec/grammar.ebnf` and the tree-sitter grammar move in lockstep during
the migration; cross-repo coordination overhead while iterating would
slow Phase 1. When the grammar reaches full EBNF coverage and stabilises,
it gets extracted to `hyperpolymath/tree-sitter-twasm` for the Linguist
+ npm publication step (Phase 4 deliverable).

## Building and testing

Requires `tree-sitter-cli` (install via `npm install -g tree-sitter-cli`
or `cargo install tree-sitter-cli`):

```bash
cd tools/tree-sitter-twasm
tree-sitter generate      # generate parser from grammar.js
tree-sitter test          # run corpus tests
tree-sitter parse ../../examples/01-single-module.twasm  # parse a real example
```

The generated `src/parser.c` and `src/grammar.json` are gitignored;
regenerate locally via `tree-sitter generate`.

## How this fits the production path

| Phase | This grammar's role |
|-------|---------------------|
| **0** (now) | Scaffold + region-decl coverage; proves toolchain works |
| **1** | Extend to full `spec/grammar.ebnf` parity; back the Idris2 parser |
| **4** | Extract to `hyperpolymath/tree-sitter-twasm`; publish to npm; submit to Linguist |

Tracked under issue [#48 (Phase 0)](https://github.com/hyperpolymath/typed-wasm/issues/48).
