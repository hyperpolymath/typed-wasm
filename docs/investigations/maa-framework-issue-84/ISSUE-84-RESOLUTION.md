# Issue #84 — Resolution: `absolute-zero/` is a STALE VENDOR COPY (Option B, pure submodule)

**Repo:** hyperpolymath/maa-framework · **Issue:** #84 · **Related:** PR #82 (merged, classifies markers), PR #83 (re-vendor to upstream)
**Decision:** **(B) Stale vendor copy.** Replace the in-tree `absolute-zero/` subtree with a git
submodule pinned to upstream `hyperpolymath/absolute-zero`. **Nothing needs to be extracted first.**

> **Evidence basis = authoritative.** Both repos were `git clone`d and compared with real `diff` on
> local disk. Earlier figures in this thread that came from the WebFetch summariser / async sub-agents
> were unreliable (one hallucinated a 1047-line `QuantumCNO.v`; another invented a `ci.yml`). **Ignore
> those. Only the numbers below — from `diff` against the clones — are real.**

Compared: `maa @ 9dbf56b` (subtree `absolute-zero/`) vs `upstream @ 7da92b360deacb31d6fc8a2121da57ed6f47f4f9` (2026-05-30).

---

## 1. Decision & rationale (one paragraph)

maa-framework's `absolute-zero/` is a **clean, slightly-stale subset of upstream** — a vendor copy,
**not a fork, not a hybrid**. A full recursive diff of the whole subtree shows only **1 maa-unique
file** (an inert nested CI workflow), **15 differing files** (every one of which is *upstream-ahead*),
and **2 upstream-only files**. Critically, **no proof file contains any maa-only theorem or any proof
that upstream leaves open** — so converting the subtree to a submodule **destroys no proof work**. This
keeps PR #82's `§(e) VENDORED` classification correct and makes "resolution path = upstream"
structurally true. Hybrid (C) is ruled out because there is no fork component anywhere in the tree.

**#84's premise is stale.** Its "files unique to maa / missing from maa / 3 drifted proof files" lists
describe the state **before PR #83** ("re-vendor absolute-zero/ subtree to upstream HEAD", 27 May). The
files it calls "unique to maa" (`EchoBridgeCNO.agda`, `EchoBridgeScaffold.agda`, `ECHIDNA_*`,
`examples/go`, …) are now **byte-identical to upstream** (verified by sha256) — they are *not* maa-only.
#83 already did the convergence; the submodule swap is the clean finish.

---

## 2. Authoritative whole-subtree diff

| Category | Count | Detail |
|---|---:|---|
| **Only in maa** | **1** | `.github/workflows/jekyll-gh-pages.yml` — a Pages workflow in the *nested* vendored `.github/` (inert: nested workflows don't run). The only human-glance item; near-certainly disposable. |
| **Differ** | **15** | 6 proof files (all upstream-ahead, §3) + 9 infra files: `.github/workflows/{governance,hypatia-scan,rust-ci,scorecard}.yml`, `.gitignore`, `.machine_readable/META.scm`, `docs/proof-debt-triage.md`, `docs/proof-debt.md`, `proofs/coq/_CoqProject`. All are stale vendored-copy infra, not maa customisations. |
| **Only in upstream** | **2** | `proofs/coq/common/PhysicsConstants.v`, `proofs/coq/common/StatMechBasis.v` — the refactored shared-axiom modules maa predates (see §3). |

`docs/proof-debt.md` note: the *differing* one here is the copy **inside** `absolute-zero/` (upstream's
own, maa's is the 246-line pre-refactor version vs upstream's 423-line current; neither mentions
"maa-framework"). maa-framework's **own** repo-root `docs/proof-debt.md` from PR #82 lives **outside**
the subtree and is **not touched** by the swap.

---

## 3. The 6 differing proof files — direction = upstream-ahead (safe)

Open-goal counts (`Admitted/admit/Axiom/Parameter/sorry`) and maa-only proven-theorem counts, both
sides, from `grep`/`diff` on the clones:

| File | maa (Ax/Param, lines) | upstream (Ax/Param, lines) | maa-only theorems | maa-only proofs | Verdict |
|---|---|---|---:|---:|---|
| coq/physics/LandauerDerivation.v | 14 / 7, 353 | 7 / 4, 349 | 0 | 0 | **BEHIND** |
| coq/physics/StatMech.v | 10 / 4, 411 | 3 / 1, 385 | 0 | 0 | **BEHIND** |
| coq/quantum/QuantumCNO.v | 29 / 16, 622 | 27 / 14, 691 | 0 | 0 | **BEHIND** |
| coq/quantum/QuantumMechanicsExact.v | 3 / 1, 423 | 1 / 1, 428 | 0 | 0 | **BEHIND** |
| lean4/QuantumCNO.lean | 0 / 0, 260 | 0 / 0, 292 | 0 | 0 | **BEHIND** |
| lean4/StatMech.lean | 0 / 0, 203 | 0 / 0, 237 | 0 | 0 | **BEHIND** (strict subset: 0 maa-only lines) |

- **0 sorry / 0 admit / 0 Admitted** on either side, every file.
- maa shows *more* axioms only because it's **pre-refactor**: maa inlines `kB`, `temperature`,
  `prob_nonneg`, `shannon_entropy_*`, etc.; upstream factored these into the new shared modules
  `common/PhysicsConstants.v` ("Single source of truth for [kB] and [temperature]") and
  `common/StatMechBasis.v` ("Shared Probability + Entropy Axioms"), wired via upstream's `_CoqProject`
  (`+common/PhysicsConstants.v`, `+common/StatMechBasis.v`). The 2 maa-only quantum axioms
  (`kB_positive`, `temperature_positive`) are ABSENT upstream for exactly this reason.
- maa's only unique lines in the two flagged quantum files are **comments** ("X gate is NOT a CNO",
  "Hadamard gate is NOT a CNO") — no proof content.

→ **Every overlapping proof is equal-or-behind upstream. The submodule swap loses nothing.** This is
the disambiguator #84 requested ("inspect the drifted files") — it resolves cleanly to **vendor**.

Corroborating intent-to-track (not fork): PR #82 (merged) labels all 150 markers `§(e) VENDORED`;
history goes `"Fix stale submodule pointers after repo cleanup"` (3 Mar) → `"re-vendor … to upstream
HEAD"` (#83, 27 May); vendored files still carry `Project: Absolute Zero` + original author (no rebrand).

---

## 4. Plan (pure submodule conversion — no extraction step)

1. **Re-verify in the maa checkout** (the one command that gates everything):
   ```bash
   git clone https://github.com/hyperpolymath/absolute-zero /tmp/az
   git -C /tmp/az checkout 7da92b360deacb31d6fc8a2121da57ed6f47f4f9
   diff -rq --exclude=.git absolute-zero /tmp/az
   # expect: 1 "Only in absolute-zero" (jekyll-gh-pages.yml), 15 "differ", 2 "Only in /tmp/az"
   ```
   Eyeball `jekyll-gh-pages.yml`; if it's a stock Pages deploy (it is), let it go.
2. `git rm -r absolute-zero`
3. `git submodule add https://github.com/hyperpolymath/absolute-zero absolute-zero` then
   `git -C absolute-zero checkout 7da92b360deacb31d6fc8a2121da57ed6f47f4f9`.
   Optional `sparse-checkout set proofs/coq proofs/lean4 proofs/agda` if only the proof subset is wanted
   (default recommendation: take the whole sibling — that's the point of an estate-sibling submodule).
4. Wire `git submodule update --init --recursive` into checkout/CI; update any `Justfile`/CI/build paths
   that referenced `absolute-zero/…`. Keep maa-framework's repo-root `docs/proof-debt.md` (#82) as-is;
   add a note that the 150 markers' canonical home is now the submodule.
5. Open a **draft PR** for the conversion; **close #84** with the §5 comment.

Guarded script for steps 1–3: `convert-to-submodule.sh`.

---

## 5. Paste-ready comment for #84

> **Decision: (B) — stale vendor copy. Convert `absolute-zero/` to a submodule. No extraction needed.**
>
> Cloned both repos and diffed the whole subtree against upstream `absolute-zero@7da92b3` (current
> HEAD). Authoritative result:
>
> | category | count | what |
> |---|---:|---|
> | only in maa's `absolute-zero/` | 1 | `.github/workflows/jekyll-gh-pages.yml` (inert nested Pages workflow) |
> | differ | 15 | 6 proof files + 9 stale infra files |
> | only upstream | 2 | `proofs/coq/common/{PhysicsConstants,StatMechBasis}.v` |
>
> **All 6 differing proof files are upstream-ahead** — 0 maa-only theorems, 0 maa-only proofs, 0
> `sorry`/`admit`/`Admitted` on either side. maa simply carries *more inlined axioms* because it predates
> upstream's refactor of `kB`/`temperature`/Shannon axioms into the two new shared `common/` modules.
> So there's **no maa-only proof work and no fork** — a submodule swap loses nothing but an inert CI file.
>
> Heads-up: this issue's unique/missing-file lists are **stale** — they predate PR #83 ("re-vendor to
> upstream HEAD"). The files it calls "unique to maa" (`EchoBridge*.agda`, `ECHIDNA_*`, `examples/go`,
> `proofs/coq/quantum/`) are now byte-identical to upstream (sha256-verified); maa is just behind.
>
> **Plan:** (1) `git rm -r absolute-zero`; (2) re-add as a submodule pinned to `7da92b3`; (3) wire
> `git submodule update --init` into CI; (4) keep PR #82's `§(e) VENDORED` classification — the submodule
> makes "resolve upstream" structurally true.
>
> Resolves #84 (completing what #83 started).
