# typed-wasm

**Progressive type safety for WebAssembly linear memory** — checked L1–L10 core, 0 `believe_me`, formal Idris2 proofs.

## Status

Pre-alpha / research. Foundation defensibly engineered as of 2026-05-24; proof-debt long-tail items closed in a 2026-05-27 sweep. See [Phase-0-Status](Phase-0-Status) for the engineering surface, and [Proof-Debt-Status](Proof-Debt-Status) for what's mechanically proven, what's outstanding, and what's blocked.

The path from here to a production-quality compile target adopted outside the hyperpolymath ecosystem is laid out as a 6-phase plan in [Production-Path](Production-Path) and [`docs/PRODUCTION-PATH.adoc`](https://github.com/hyperpolymath/typed-wasm/blob/main/docs/PRODUCTION-PATH.adoc). See [Comparison](Comparison) for how typed-wasm sits among neighbouring approaches at each maturity level.

## What it is

WebAssembly's linear memory is an untyped byte array — structurally identical to a schemaless database where programs issue untyped queries. typed-wasm adds **schemas** (regions) and **type-safe access operations** (typed projections through the schema), verified by the Idris2 prover at compile time with zero runtime overhead.

```
region Players[100] {
    hp:    i32;
    speed: f64;
    pos:   @Vec2;
    name:  u8[24];
    where 0 <= hp <= 9999;
    align 8;
}
```

Loads compile to bare wasm `i32.load` / `i64.load` / `f32.load` / `f64.load` at computed offsets. The verifier proves each access is within bounds, has the right type, and respects ownership / lifetime / linearity rules.

## The killer feature

When Module A (compiled from Rust) shares wasm linear memory with Module B (compiled from ReScript or AffineScript or Ephapax), **neither source-level type system can verify the boundary**. Rust's borrow checker types memory within Rust; ReScript's type system types values within ReScript. typed-wasm declares the shared schema once, both modules import it, and the checker verifies structural agreement at compile time before any module runs.

## The 10 levels

| Level | What it guarantees |
|-------|---|
| L1 | Instruction validity (parse-time) |
| L2 | Region binding (schema lookup) |
| L3 | Type-compatible access (field type matching) |
| L4 | Null safety (opt<T> tracking) |
| L5 | Bounds-proof (compile-time offset verification) |
| L6 | Result-type (access return type known) |
| L7 | Aliasing safety (exclusive mutable refs) |
| L8 | Effect-tracking (Read/Write/Alloc/Free) |
| L9 | Lifetime safety (no use-after-free) |
| L10 | Linearity (exactly-once resource usage) |

Levels are progressive — you cannot skip from L1 to L7. L11 (tropical cost-tracking) and L12 (epistemic safety) exist as research-draft Idris2 modules but aren't claimed as part of the checked core.

## Architecture

Follows the hyperpolymath ABI-FFI standard:

- **Idris2 ABI** (`src/abi/TypedWasm/ABI/`) — formal dependent-type proofs; 0 `believe_me`, 0 `assert_total`, 0 `postulate`. Includes `TypedWasm.ABI.VerifierSpec` (added 2026-05-27 via PR #79) as the Idris2 spec-of-record for the Rust post-codegen verifier — with totally-proven `VerifierSpecAgreement` / `SourceVerifierAgreement` records bridging the spec to verifier and source-checker. See [Proof-Debt-Status](Proof-Debt-Status) for the inventory.
- **Zig FFI** (`ffi/zig/`) — C-ABI bridge for runtime region management + typed load/store
- **Rust verifier** (`crates/typed-wasm-verify/`) — post-codegen verification of the 10-level discipline against compiled wasm
- **Surface syntax** (`spec/grammar.ebnf`) — `.twasm` source format (EBNF)
- **Tree-sitter grammar** (`tools/tree-sitter-twasm/`) — scaffold; region-decls coverage in v0, full parity Track A deliverable
- **ReScript parser** (`src/parser/`) — current parser; being replaced by Idris2 parser in Track A

## Quick start

```bash
# Rust verifier — 10/10 tests passing
cargo build --workspace --locked
cargo test --workspace --locked

# Idris2 proofs (when toolchain available)
cd src/abi && idris2 --build typed-wasm.ipkg

# ReScript parser smoke
npm install
node_modules/.bin/rescript build
node tests/smoke/e2e-smoke.mjs

# Zig FFI
cd ffi/zig && zig build test
```

## Related projects

- [TypeLL](https://github.com/hyperpolymath/typell) — type theory foundation (typed-wasm is one application)
- [TypedQLiser](https://github.com/hyperpolymath/typedqliser) — same principle applied to database queries
- [VCL-total](https://github.com/hyperpolymath/vql-ut) — same levels applied to database queries (sibling)
- [AffineScript](https://github.com/hyperpolymath/affinescript) — compiles to WasmGC; uses typed-wasm as aggregate library
- [Ephapax](https://github.com/hyperpolymath/ephapax) — compiles to WasmGC; consumes typed-wasm-verify
- [ECHIDNA](https://github.com/hyperpolymath/echidna) — property-based testing of proof soundness

## License

MPL-2.0. See [LICENSE](https://github.com/hyperpolymath/typed-wasm/blob/main/LICENSE).

## Author

Jonathan D.A. Jewell &lt;j.d.a.jewell@open.ac.uk&gt;
