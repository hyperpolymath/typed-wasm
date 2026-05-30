# Handoff — paste into a Claude Code session scoped to hyperpolymath/maa-framework

Resolve issue #84 ("is `absolute-zero/` a deliberate fork or stale vendor copy?").

DECISION (made, HIGH confidence, verified by real `git diff` of both clones):
**(B) stale vendor copy — convert `absolute-zero/` to a git submodule. NO extraction needed.**

Authoritative findings — maa@9dbf56b subtree vs upstream `absolute-zero`@7da92b360deacb31d6fc8a2121da57ed6f47f4f9:
- 1 file only in maa: `.github/workflows/jekyll-gh-pages.yml` (inert nested Pages workflow → drop)
- 15 differing files: 6 proof files + 9 stale infra files. ALL 6 proof files are UPSTREAM-AHEAD:
  0 maa-only theorems, 0 maa-only proofs, 0 sorry/admit/Admitted either side. maa just has more
  inlined axioms because it predates upstream's refactor of kB/temperature/Shannon axioms into the
  new shared modules proofs/coq/common/PhysicsConstants.v + StatMechBasis.v.
- 2 files only upstream: those two new common/ modules.
=> No maa-only proof work anywhere. Submodule swap loses nothing but the inert CI file.

#84's premise is STALE (pre-PR #83 "re-vendor to upstream HEAD"). The files it calls "unique to maa"
(EchoBridge*.agda, ECHIDNA_*, examples/go, proofs/coq/quantum/) are now byte-identical to upstream
(sha256-verified). maa is simply behind.

DO THIS:
1. Re-verify (gates everything):
   git clone https://github.com/hyperpolymath/absolute-zero /tmp/az
   git -C /tmp/az checkout 7da92b360deacb31d6fc8a2121da57ed6f47f4f9
   diff -rq --exclude=.git absolute-zero /tmp/az   # expect 1 only-in-maa (jekyll), 15 differ, 2 only-upstream
   Eyeball jekyll-gh-pages.yml; if stock Pages deploy, drop it.
2. git rm -r absolute-zero
3. git submodule add https://github.com/hyperpolymath/absolute-zero absolute-zero
   git -C absolute-zero checkout 7da92b360deacb31d6fc8a2121da57ed6f47f4f9
   (optional: sparse-checkout set proofs/coq proofs/lean4 proofs/agda)
4. Add `git submodule update --init --recursive` to CI/checkout; fix any Justfile/CI/build paths.
   Keep repo-root docs/proof-debt.md (PR #82); note the 150 markers' canonical home is now the submodule.
5. Open a DRAFT PR; post the prepared comment on #84 (it's in §5 of ISSUE-84-RESOLUTION.md) and close #84
   referencing the PR.

Guarded script for steps 1–3: convert-to-submodule.sh (has a hard stop if any unexpected maa-only path appears).
