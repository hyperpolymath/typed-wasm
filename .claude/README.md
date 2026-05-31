<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# `.claude/` — Claude Code project configuration

Checked-in, team-shared configuration for Claude Code sessions on typed-wasm.

## Contents

| Path | Purpose |
|------|---------|
| `CLAUDE.md` | Project instructions (overview, architecture, build/test, the 10 levels). |
| `settings.json` | Permissions allowlist + hooks (see below). |
| `hooks/governance-precheck.sh` | Local mirror of two CI governance gates. |

## `settings.json`

### Permissions (`permissions.allow`)

A **non-destructive** allowlist that cuts permission prompts for the commands used routinely in
this repo: read-only git inspection (`status/log/diff/fetch/show/ls-files/ls-tree/branch/
rev-parse/merge-base/for-each-ref/check-attr`, `git bundle verify`/`list-heads`), the cargo
build/test/lint loop (`cargo build/test/clippy`, `cargo fmt --check`, `cargo metadata/audit` —
these touch only `target/`, never the source tree), `diff -rq`, and `curl` **restricted to
`https://raw.githubusercontent.com/`** (used to compare sibling-estate repos without a full
clone). No push, no source-mutating, and no destructive commands are granted — those still
prompt.

### Hooks (`hooks.SessionStart`)

Runs `hooks/governance-precheck.sh` at session start. **Advisory only — never blocks, always
exits 0.** It surfaces, before you push, the two CI gates most easily tripped by docs changes:

1. **Empty-linter** — invisible/zero-width Unicode (NBSP, ZWSP, BOM, bidi marks, NUL) in source
   files, using the exact byte patterns from `.github/workflows/dogfood-gate.yml`.
2. **SPDX headers** — `SPDX-License-Identifier` presence on any `.md` / `.sh` / `.adoc`
   **changed vs `origin/main`** (the push delta — not the whole tree, to avoid the pre-existing
   unlicensed-doc backlog and stay accurate to "catch before push").

Review or disable hooks anytime via the `/hooks` menu.

> Note: the settings watcher only picks up `.claude/settings.json` if it existed when the
> session started. On the session that first adds this file, open `/hooks` once (or restart)
> to load the hook.
