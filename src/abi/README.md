<!--
SPDX-License-Identifier: PMPL-1.0-or-later
Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-->

# src/abi — Idris2 ABI Layer

This directory contains the Idris2 formal proofs for both roles of `typed-wasm`
(see ADR-004 in `.machine_readable/6a2/META.a2ml`).

## Directory Layout

```
src/abi/
├── TypedWasm/ABI/          ← Role 1: TypeLL type safety for WasmGC linear memory
│   ├── Levels.idr           Type safety level hierarchy (L1-L10 initial mapping)
│   ├── Region.idr           Region schema proofs
│   ├── TypedAccess.idr      Type-safe access operation proofs
│   ├── Pointer.idr          Pointer safety proofs
│   ├── MultiModule.idr      Multi-module shared memory proofs
│   ├── Effects.idr          Effect tracking proofs
│   ├── Lifetime.idr         Lifetime safety (no use-after-free)
│   ├── Linear.idr           Linearity proofs (QTT)
│   ├── Tropical.idr         Tropical type extensions (L11+ research)
│   ├── Epistemic.idr        Epistemic type extensions (L12+ research)
│   └── Proofs.idr           Top-level proof bundle
│
├── layout/                  ← Role 2: Cross-language layout contracts (aggregate library)
│   ├── Types.idr            Agreed WasmGC type layouts (Option, Result, String, ...)
│   └── ABI.idr              Cross-language calling conventions
│
└── typed-wasm.ipkg          Idris2 package file (covers TypedWasm/ABI/ only)
```

## Role Separation

**`TypedWasm/ABI/`** is the primary role: the TypeLL progressive type safety proofs
for WasmGC linear memory.  These proofs are part of the default checked package
(`typed-wasm.ipkg`).  No `believe_me` is permitted here.

**`layout/`** is the secondary role: formally verified type layout and ABI
conventions for languages that compile to typed WasmGC (AffineScript, Ephapax).
These proofs are developed separately from the TypeLL level hierarchy because
the two concerns — WASM memory safety and cross-language interop — are
independent.  They share the same Idris2 tooling but are not logically coupled.

## Pipeline Position

```
katagoria  →  typell  →  typed-wasm  →  PanLL
                              ↑
                     both subtrees live here
```

Type theory ideas originate in `katagoria` (research), are promoted to `typell`
(the open-ended progressive verification kernel), and applied here:
- `TypedWasm/ABI/` applies TypeLL to WASM memory safety
- `layout/` applies Idris2 ABI methodology to cross-language binary conventions
