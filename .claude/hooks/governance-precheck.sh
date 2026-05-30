#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# governance-precheck.sh — local mirror of two CI governance gates, run at SessionStart so
# CI failures are caught at source before push. Advisory only: NEVER blocks, always exits 0.
#   1. Empty-linter: invisible/zero-width Unicode in source files (dogfood-gate.yml).
#   2. SPDX header presence on .md / .sh / .adoc CHANGED vs origin/main (licence-consistency).
# Output is surfaced to the model via the SessionStart hook's stdout.
set +e

cd "${CLAUDE_PROJECT_DIR:-.}" 2>/dev/null || exit 0
command -v git >/dev/null 2>&1 || exit 0
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || exit 0

# --- 1. Empty-linter: exact invisible-char byte patterns from .github/workflows/dogfood-gate.yml ---
PATTERNS='\xc2\xa0|\xe2\x80\x8b|\xe2\x80\x8c|\xe2\x80\x8d|\xef\xbb\xbf|\xc2\xad|\xe2\x80\x8e|\xe2\x80\x8f|\xe2\x80\xaa|\xe2\x80\xab|\xe2\x80\xac|\xe2\x80\xad|\xe2\x80\xae|\x00'
INVIS=$(git ls-files -z -- \
          '*.rs' '*.ex' '*.exs' '*.affine' '*.js' '*.ts' '*.json' '*.toml' \
          '*.yml' '*.yaml' '*.md' '*.adoc' '*.idr' '*.zig' '*.v' '*.jl' \
          '*.gleam' '*.hs' '*.ml' '*.sh' 2>/dev/null \
        | xargs -0 grep -PlZ "$PATTERNS" 2>/dev/null | tr '\0' '\n' | grep -c .)

# --- 2. SPDX header presence on docs/scripts CHANGED vs origin/main ---
# Scoped to the push delta (not the whole tree) so it flags only what THIS branch adds/edits —
# accurate to "catch before push" and avoids the pre-existing unlicensed-doc backlog.
BASE=$(git rev-parse --verify -q origin/main || git rev-parse --verify -q main)
MISSING_SPDX=""
if [ -n "$BASE" ]; then
  while IFS= read -r f; do
    [ -z "$f" ] && continue
    [ -f "$f" ] || continue   # skip deletions
    case "$f" in *.sh|*.md|*.adoc) ;; *) continue ;; esac
    head -5 "$f" 2>/dev/null | grep -q 'SPDX-License-Identifier' || MISSING_SPDX="${MISSING_SPDX}${f}\n"
  done < <(git diff --name-only --diff-filter=AM "$BASE"...HEAD 2>/dev/null)
fi
MISSING_COUNT=$(printf '%b' "$MISSING_SPDX" | grep -c .)

if [ "${INVIS:-0}" -eq 0 ] && [ "${MISSING_COUNT:-0}" -eq 0 ]; then
  echo "governance-precheck: OK — no invisible chars; SPDX headers present on tracked docs/scripts."
else
  echo "governance-precheck: ADVISORY (fix before pushing — these mirror CI gates):"
  [ "${INVIS:-0}" -ne 0 ]        && echo "  • $INVIS file(s) contain invisible/zero-width Unicode (empty-linter gate)."
  if [ "${MISSING_COUNT:-0}" -ne 0 ]; then
    echo "  • $MISSING_COUNT tracked doc/script(s) missing an SPDX-License-Identifier header:"
    printf '%b' "$MISSING_SPDX" | grep . | sed 's/^/      /'
  fi
fi
exit 0
