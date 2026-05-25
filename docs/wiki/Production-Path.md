# Production Path

The canonical 6-phase plan from pre-alpha / research to production-quality compile target. Long-form companion to [`docs/PRODUCTION-PATH.adoc`](https://github.com/hyperpolymath/typed-wasm/blob/main/docs/PRODUCTION-PATH.adoc) in the repo.

## Scope

"Production-ready as a compile target equivalent to wasm" admits three readings — this plan targets only **reading 1**:

1. **Serious-systems compile target adopted outside hyperpolymath.** A toolchain an outside team can pick up, integrate, and ship without direct maintainer support; stable spec, conformance suite, multi-language SDKs, runtime that enforces the full level set. **← this plan**
2. *W3C-standardized bytecode peer to wasm.* Out of scope. Wasm took 5 years and Mozilla+Google+Apple+Microsoft. Realistic stretch goal at Phase 5: WebAssembly CG candidate extension.
3. *Own bytecode runtimes execute natively, not compiled-to-wasm.* Out of scope. Would require building a wasm-class platform from scratch.

## The six phases

| Phase | Theme | Duration | Gate to next |
|---|---|---|---|
| **0** | Stabilize foundation | weeks (mostly done) | CI green, no merged red, ROADMAP truthful |
| **1** | End-to-end producer | 4–6 months | `.twasm → .wasm` round-trips for all examples |
| **2** | Multi-producer adoption | 6–12 months | ≥3 independent producers ship verified wasm |
| **3** | Runtime-side enforcement | 9–18 months | Reference runtime detects L7+ producer violation |
| **4** | Tooling + DX | 12–24 months | Outside-ecosystem ship without maintainer support |
| **5** | Spec + standards | 18–36 months | 1.0 frozen, conformance suite, academic publication |
| **6** | Production hardening | 24–36 months | SLA + CVE + ≥1 production deployment + case study |

Phases overlap. Cumulative timeline: 2–3 years well-resourced, 4–5 years single-maintainer part-time.

## What each phase delivers

### Phase 0 — Stabilize the foundation

Close the engineering-surface fragility around the proofs. PRs were merging with red CI; the verifier job we added to catch wasmparser breaks was itself silently broken. Phase 0 fixes that gap.

**Tracks**: A (codegen pipeline kickoff: tree-sitter grammar → Idris2 parser → ReScript cut → codegen v0), B (AffineScript verifier-binary swap), C (audit-floor cleanup: cargo audit, property tests, Security aspect, proof-level regression tests).

See [Phase-0-Status](Phase-0-Status) for current closure state.

### Phase 1 — End-to-end producer

The phase that turns typed-wasm from "verifier + spec" into "compile target proper".

Codegen for all 10 levels, all 6 example `.twasm` files. Round-trip soundness as ECHIDNA property tests. Optimisation story (binaryen pass list or in-tree passes). WAT debug emission. Source maps. Human-readable error messages. Multi-module codegen at verifier parity.

### Phase 2 — Multi-producer adoption

Today AffineScript is the only realistic adopter. For typed-wasm to be a real target, other compilers must target it.

Producer specification (normative). C ABI for the verifier. Producer conformance test suite. "How to make your compiler target typed-wasm" cookbook built from the AffineScript migration. ≥2 more reference producers beyond AffineScript. LLVM lowering guide.

### Phase 3 — Runtime-side enforcement

The hard one. Today L7–L10 are compile-time guarantees only. Runtimes know nothing about regions. A malicious or buggy producer can violate them at runtime and no one notices.

Options: Wasmtime fork (recommended), Wasmer plugin, native compilation, WebAssembly CG proposal.

### Phase 4 — Tooling and DX

LSP, debugger integration, editor plugins (VS Code / JetBrains / Neovim / Emacs / Helix / Zed), Linguist registration, package conventions, complete documentation suite, conference talks + papers, real-world examples.

### Phase 5 — Specification and standards

Freeze 1.0 spec. Conformance test suite at wasm-spec-interpreter tier. Multiple independent verifier implementations. Academic publication. W3C CG submission. Security review.

### Phase 6 — Production hardening

SLA, CVE process, performance benchmarks, long-running production deployment, migration guides, multi-language SDK quality, published case studies. Plus ≥2 committers with release authority (bus-factor fix).

## Six load-bearing decisions

Each should land an ADR under `docs/decisions/` when made:

1. **D1**: Stay codegen-on-top-of-wasm vs. become own bytecode
2. **D2**: Producer-side-only vs. runtime-aware (gates Phase 3)
3. **D3**: W3C CG path vs. independent ecosystem
4. **D4**: Idris2-only proofs vs. dual implementation
5. **D5**: MPL-2.0 vs. dual MPL/Apache
6. **D6**: Single-maintainer vs. recruit committers

## Tracking

GitHub issues with `phase:N` labels:

| Phase | Issue |
|---|---|
| 0 | [#48](https://github.com/hyperpolymath/typed-wasm/issues/48) |
| 1 | [#49](https://github.com/hyperpolymath/typed-wasm/issues/49) |
| 2 | [#50](https://github.com/hyperpolymath/typed-wasm/issues/50) |
| 3 | [#51](https://github.com/hyperpolymath/typed-wasm/issues/51) |
| 4 | [#52](https://github.com/hyperpolymath/typed-wasm/issues/52) |
| 5 | [#53](https://github.com/hyperpolymath/typed-wasm/issues/53) |
| 6 | [#54](https://github.com/hyperpolymath/typed-wasm/issues/54) |
