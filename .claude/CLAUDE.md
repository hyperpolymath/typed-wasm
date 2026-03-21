# typed-wasm — Project Instructions

## Overview

TypeLL's 10-level type safety for WebAssembly linear memory.

**Status:** pre-alpha / research
**Core insight:** WASM linear memory is a schemaless database. typed-wasm adds schemas (regions) and type-safe queries (typed access operations).
**Killer feature:** Multi-module shared memory type safety across language boundaries.

## Architecture

- **Idris2 ABI** (`src/abi/`) — Formal proofs: region schemas, typed access, 10-level verification
- **Zig FFI** (`ffi/zig/`) — C-ABI bridge: runtime region management, typed load/store
- **Grammar** (`spec/grammar.ebnf`) — The `.twasm` surface syntax (EBNF)
- **Spec** (`spec/10-levels-for-wasm.adoc`) — How each level maps from DB to WASM
- **Examples** (`examples/`) — `.twasm` files demonstrating all features

## Build & Test

```bash
# Zig FFI
cd ffi/zig && zig build test

# Idris2 ABI (when Idris2 toolchain available)
cd src/abi && idris2 --check Proofs.idr
```

## Key Design Decisions

- Follows hyperpolymath ABI-FFI standard (Idris2 ABI, Zig FFI)
- PMPL-1.0-or-later license
- RSR (Rhodium Standard Repository) template
- Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
- File extension: `.twasm` for typed-wasm source files
- NO believe_me, assert_total, or unsafe patterns in Idris2 code
- Region schemas are immutable once declared
- 10 levels are progressive (cannot skip)

## Integration Points

- **TypeLL**: Type theory foundation — typed-wasm implements TypeLL's levels for WASM
- **TypedQLiser**: Could become a TypedQLiser plugin (WASM as a "query target")
- **VQL-UT**: Sibling project — same levels, different domain (database vs memory)
- **ECHIDNA**: Property-based testing of proof soundness
- **GraalVM/Truffle**: Potential future target for the same approach

## The 10 Levels for WASM

1. Instruction validity (parse-time)
2. Region-binding (schema lookup)
3. Type-compatible access (field type matching)
4. Null safety (opt<T> tracking)
5. Bounds-proof (compile-time offset verification)
6. Result-type (access return type known)
7. Aliasing safety (exclusive mutable refs)
8. Effect-tracking (Read/Write/Alloc/Free)
9. Lifetime safety (no use-after-free)
10. Linearity (exactly-once resource usage)
