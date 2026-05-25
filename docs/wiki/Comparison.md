# Comparison Landscape

Where typed-wasm sits among neighbouring approaches at each maturity level. Approximate; the wasm-safety landscape moves fast.

## Today (early Phase 0, ~v0.1)

Honest peer set: **academic research prototypes for wasm memory safety**.

| Project | What it does | typed-wasm comparison |
|---|---|---|
| **MS-Wasm** (Disselkoen et al. 2019+) | Segmented memory model, runtime enforcement of bounds, hot/cold heap separation | Closest peer in ambition. typed-wasm is **stronger in formal foundation** (Idris2 proofs vs. paper proofs), **weaker in deployment** (no published runtime), **broader in scope** (L7–L10 reach beyond bounds) |
| **CHERI-Wasm** (Watson et al.) | Capability-machine extension for wasm, hardware-level enforcement | Different threat model. CHERI = runtime-hardware. typed-wasm = compile-time-discipline. Complementary, not competing |
| **WAVM / wasm-validate / wasmparser** | Well-formedness validators | typed-wasm is strictly stronger: every typed-wasm-valid program is wasm-valid, but not vice versa. Different niche |
| **AssemblyScript runtime** | Managed types + GC over linear memory | Same "type safety for wasm" niche, opposite angle (managed types vs. linear-region discipline). Production-deployed; typed-wasm is not |
| **Lucet** (Fastly, archived) | Sandbox isolation for wasm-as-FaaS | Different concern (host safety, not producer-side memory discipline) |

At start of Phase 0, typed-wasm sits roughly where MS-Wasm was at its initial publication: a credible academic prototype with formal claims and a verifier, lacking the runtime story and production deployment. It would be the **only** entry in that peer set with machine-checked end-to-end proofs (the others have paper proofs or are unverified).

## After Phase 0 (foundation stabilized, ~v0.2)

Still a research prototype, but a **defensibly engineered** one. CI is honest; codegen v0 works for the simplest example; the ReScript-to-Idris2 parser migration has happened; the AffineScript adoption is real and working. Peer set unchanged but typed-wasm has moved from "interesting paper-ware" to "interesting paper-ware you can build and run without hand-holding".

This is *not yet* "a fully legit and working verified soundness discipline for wasm linear memory" in any sense an outsider would recognise. It is a credible research vehicle.

## After Phase 1 (end-to-end producer, ~v0.5 beta)

First version that warrants the description "**a working compile target with verified soundness for linear memory**". A user can take a `.twasm` source, compile it, and trust the 10-level discipline.

Peer set shifts: typed-wasm becomes comparable to **AssemblyScript** as a language-with-a-wasm-toolchain, but with a much stronger safety story. Still pre-1.0; still single-maintainer; still ecosystem-confined.

## After Phase 2 (multi-producer adoption, ~v0.9 RC)

typed-wasm enters the same category as **wasm-bindgen** (the standard "wasm + multi-language interop" surface) but with formal guarantees on top.

Three independent producers exist; the spec is stable enough that the second and third adoptions did not require spec changes. At this point typed-wasm is "**the standard way to opt into formal memory safety for any wasm producer**". Peer set: it has no direct peer at this maturity level; the closest comparison is **CHERI's adoption status** in the hardware world (specified, multi-vendor, used but not pervasive).

## After Phase 3 (runtime-side enforcement, ~v1.0)

typed-wasm becomes one of a small set of **memory-safe wasm-class platforms** with both producer- and runtime-side enforcement. Peer set:

| Project | Approach |
|---|---|
| **CHERI / Morello + wasm** | Hardware capability machine running wasm with capability-aware runtime |
| **MS-Wasm production runtime** (hypothetical) | If MS-Wasm reaches production by then |
| **wasmGC** | Different threat model (managed types) but addresses overlapping concerns from the other direction |

Within this set, typed-wasm's distinguishing claim is **the formal proof of soundness of its level discipline** (Idris2). CHERI has hardware proofs; wasmGC has wasm-spec coverage; MS-Wasm has paper proofs. typed-wasm would be unique in carrying machine-checked end-to-end proofs from spec to producer to runtime.

## After Phase 6 (production-hardened, v1.x stable)

Honest comparison is no longer to other wasm-safety projects but to **memory-safe systems languages and runtimes** in general:

| Project | Approach | What typed-wasm-1.x uniquely offers |
|---|---|---|
| **Rust** | Borrow-checker as producer-side memory safety | Rust is single-language; typed-wasm covers *any* wasm producer |
| **CHERI / Morello** | Hardware capability machine | CHERI is hardware-specific and per-runtime; typed-wasm is verifier-mediated and works on commodity hardware |
| **Pony reference capabilities** | Actor language with explicit ownership types | Pony is single-language; typed-wasm is producer-agnostic |
| **CompCert** | Verified C compiler with formal proofs | CompCert covers C → assembly; typed-wasm covers (any compiler) → wasm with stronger linearity claims |
| **wasmGC** | Managed types at the runtime level | wasmGC sidesteps linear memory; typed-wasm types linear memory directly |

typed-wasm at Phase 6 would occupy a distinct cell that **no existing system covers in one package**: machine-checked, verifier-mediated, runtime-enforced memory safety for **any wasm producer** with **cross-language sharing** verifiable end-to-end.

The closest analogue would be "Rust + CHERI + wasm" composed by hand — which no one ships as a product because the integration work is enormous and the formal coherence isn't there.

## The concrete impossibility today

If you wanted today to write a system where a Rust module and an OCaml module share wasm linear memory and you wanted machine-checked safety across that boundary, **no shipping toolchain gives you that**:

- Rust gives you borrow-checking inside Rust
- CHERI gives you runtime capability enforcement (if you have the hardware)
- MS-Wasm gives you bounds
- wasmGC sidesteps the question by using managed types instead

typed-wasm at Phase 6 is the first toolchain where that scenario works with formal guarantees.

## The honest read

typed-wasm is **uniquely positioned but unfinished**. The intellectual asset (the proofs, the 10-level discipline) is already world-class — there's nothing else with this depth of formalisation for wasm memory. The engineering surface around it is pre-alpha.

The [Production-Path](Production-Path) plan is the path from "world-class proof of concept" to "production toolchain with that proof of concept as its kernel". Phase 0 closes the engineering-fragility gap. Phase 1 makes it usable. Phases 2–6 take it to the maturity tier you'd want for shipping production wasm.

If you stop at end of Phase 1, you have "a Rust-borrowck-quality discipline you can opt any wasm producer into" — already a serious contribution. Phases 2–6 turn that into "an industry-recognised standard with multiple implementations and case studies".
