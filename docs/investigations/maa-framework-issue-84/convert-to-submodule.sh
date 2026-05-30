#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Issue #84 — convert maa-framework's vendored absolute-zero/ subtree into a submodule (Option B).
# RUN INSIDE A maa-framework CHECKOUT, on a feature branch. Review each step; nothing is forced.
#
# Authoritative local-diff audit (maa@9dbf56b subtree vs upstream@7da92b3) established:
#   * 1 file only in maa: .github/workflows/jekyll-gh-pages.yml (inert nested Pages workflow) -> drop
#   * 15 differing files: 6 proof files (ALL upstream-ahead: 0 maa-only theorems/proofs, 0 sorry)
#                         + 9 stale vendored-infra files
#   * 2 files only upstream: proofs/coq/common/{PhysicsConstants,StatMechBasis}.v (refactor maa predates)
#
# DRY-RUN VERIFIED 2026-05-30: this script ran exit-0 against a fresh maa clone; result =
#   232 files changed, 4 insertions(+), 36046 deletions(-); absolute-zero -> gitlink 160000 7da92b3.
# A prebuilt, pre-tested artifact of that result lives alongside this script (see ARTIFACTS.md):
#   issue-84-submodule.bundle  (683 B; git fetch + git merge --ff-only).
# You can apply that directly instead of running this script; this remains the from-scratch path.
#   => no maa-only proof work anywhere; the swap loses nothing but the inert CI file.
set -euo pipefail

UPSTREAM_URL="https://github.com/hyperpolymath/absolute-zero.git"
SUBTREE="absolute-zero"
PIN_SHA="7da92b360deacb31d6fc8a2121da57ed6f47f4f9"   # upstream HEAD at audit (2026-05-30); bump if desired

echo "==> 0. Safety: clean tree on a feature branch"
git rev-parse --abbrev-ref HEAD
git diff --quiet || { echo "Working tree dirty — commit/stash first."; exit 1; }

echo "==> 1. RE-VERIFY the audit before destroying anything"
TMP="$(mktemp -d)"; git clone --quiet "$UPSTREAM_URL" "$TMP/az"; git -C "$TMP/az" checkout --quiet "$PIN_SHA"
ONLY_MAA=$(diff -rq --exclude=.git "$SUBTREE" "$TMP/az" | grep "^Only in $SUBTREE" || true)
N_ONLY_MAA=$(printf '%s\n' "$ONLY_MAA" | grep -c . || true)
echo "    files only in maa subtree (expected: just jekyll-gh-pages.yml):"
printf '      %s\n' "$ONLY_MAA"
# Guard: anything maa-only OTHER than the known inert workflow must be inspected before proceeding.
UNEXPECTED=$(printf '%s\n' "$ONLY_MAA" | grep -v 'jekyll-gh-pages.yml' | grep . || true)
if [ -n "$UNEXPECTED" ]; then
  echo "    !! UNEXPECTED maa-only path(s) — STOP and inspect (may be un-upstreamed maa work):"
  printf '      %s\n' "$UNEXPECTED"; exit 1
fi
echo "    (differing proof files are upstream-ahead per audit; nothing maa-only to rescue.)"

echo "==> 2. Remove the vendored subtree (pure subset of upstream — safe)"
git rm -r "$SUBTREE"

echo "==> 3. Add the submodule, pinned"
git submodule add "$UPSTREAM_URL" "$SUBTREE"
git -C "$SUBTREE" checkout "$PIN_SHA"
git add .gitmodules "$SUBTREE"
# Optional: keep only the previously-vendored proof subset instead of the whole sibling:
#   git -C "$SUBTREE" sparse-checkout init --cone
#   git -C "$SUBTREE" sparse-checkout set proofs/coq proofs/lean4 proofs/agda

echo "==> 4. Manual follow-ups (NOT automated):"
echo "    - CI/checkout: add 'git submodule update --init --recursive'."
echo "    - Update any Justfile / CI / build paths referencing $SUBTREE/..."
echo "    - Keep repo-root docs/proof-debt.md (PR #82); note canonical marker home is now the submodule."

echo "==> 5. Review, then commit"
git status
echo "Suggested commit:"
echo "  git commit -m 'refactor(absolute-zero): convert vendored subtree to submodule pinned upstream (#84)'"
rm -rf "$TMP"
