<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# Prebuilt conversion artifacts — maa-framework #84

This was generated from a **dry-run of `convert-to-submodule.sh` against a fresh
`hyperpolymath/maa-framework` clone** (base `main @ 9dbf56b`) and **test-applied onto a pristine
clone** before being committed here. It lets a maa-framework-scoped session land the #84 submodule
conversion without re-running the script.

## What the conversion commit does

`refactor(absolute-zero): convert vendored subtree to submodule pinned upstream (#84)`

- replaces the vendored `absolute-zero/` subtree (230 files) with a **submodule gitlink**
  `160000 commit 7da92b360deacb31d6fc8a2121da57ed6f47f4f9` (upstream `absolute-zero` main HEAD at audit)
- adds `.gitmodules` → `https://github.com/hyperpolymath/absolute-zero.git`
- net diffstat: **232 files changed, 4 insertions(+), 36046 deletions(-)**

## File

| Artifact | Size | Apply with | Tested |
|---|---|---|---|
| `issue-84-submodule.bundle` | 683 B | `git fetch <bundle> refs/heads/claude/issue-84-submodule-dryrun && git merge --ff-only FETCH_HEAD` | ✓ applied onto fresh `main @ 9dbf56b`; gitlink + `.gitmodules` verified |

It's a 683-byte thin pack (the deletions need no new objects) and applies as a fast-forward onto maa
`main @ 9dbf56b` (the ref it `requires`). A full `git am` patch was deliberately omitted to keep this
docs folder free of large blobs; if you prefer `git am`, regenerate it in the maa checkout with
`git format-patch -1 <tip>` after fetching the bundle, or just re-run `convert-to-submodule.sh`.

## After applying (still required — needs write access to maa-framework)

1. `git submodule update --init --recursive`
2. Wire `git submodule update --init --recursive` into CI/checkout; fix any `Justfile`/CI/build paths
   that referenced `absolute-zero/…`.
3. Keep maa-framework's repo-root `docs/proof-debt.md` (PR #82); note the 150 markers' canonical home
   is now the submodule.
4. If branch protection requires signed commits, re-commit with your signer (the artifact commit is
   unsigned — the dry-run's signing server rejected an out-of-scope `/tmp` repo with a 400).
5. Open a **draft PR**; post the §5 comment from `ISSUE-84-RESOLUTION.md` on #84 and close it.

## Provenance / re-verify

- Base: `maa-framework` main `9dbf56b53cbbd600b9de589a85521645eca18c2f`
- Submodule pin: `absolute-zero` `7da92b360deacb31d6fc8a2121da57ed6f47f4f9`
- Verify the bundle before trusting it: `git bundle verify issue-84-submodule.bundle`
