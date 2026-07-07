<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# typed-wasm-gate

Load-time enforcement for typed-wasm — the Phase 3 slice (runtime-side
enforcement). Build-time verification trusts whoever ran the build; the
gate moves the trust boundary to the **loader**:

```rust
let verified = typed_wasm_gate::gate_module(&bytes)?;        // full verifier stack
let instance = wasmi_runtime::instantiate_verified(&engine, &mut store, &linker, &verified)?;
```

`VerifiedModule` is a witness type: its only constructors are
`gate_module` / `gate_link_graph`, which run structural validation,
L7/L10 ownership/linearity, L2 carrier bounds + access typing, and L13
region-import consistency (plus cross-module `SchemaSub` certification
for graphs, ADR-0007). The instantiation adapters accept only
`&VerifiedModule` — a violating module cannot reach a runtime through
this API because its witness never exists.

The gate itself is runtime-agnostic (bytes in, witness + `GateReport`
out). The `wasmi-runtime` feature (default) ships a pure-Rust in-process
adapter that CI executes end-to-end; a **wasmtime adapter** is the
intended follow-up and needs nothing beyond what the wasmi one uses —
compile the module from `VerifiedModule::bytes()` and instantiate.
