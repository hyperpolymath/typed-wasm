<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->

# Investigation: maa-framework issue #84 (cross-repo)

These documents resolve **`hyperpolymath/maa-framework` issue #84** — "Decide: is
`absolute-zero/` a deliberate fork or stale vendor copy?". They are parked here in
`typed-wasm` only because the analysis session was scoped to this repo; the actual
changes land in `maa-framework` (see the handoff).

**Sibling-estate context:** typed-wasm, maa-framework, and `absolute-zero` are sibling
projects in the hyperpolymath estate (ECHIDNA property-based testing of proof soundness
is a shared integration point per this repo's CLAUDE.md).

## Verdict

**(B) stale vendor copy** — convert `maa-framework/absolute-zero/` to a git submodule
pinned to upstream `hyperpolymath/absolute-zero`. No extraction needed; no maa-only proof
work exists. Established via real `git diff` of both clones (not summaries).

## Contents

| File | Purpose |
|---|---|
| `ISSUE-84-RESOLUTION.md` | Full decision, authoritative diff tables, paste-ready #84 comment |
| `convert-to-submodule.sh` | Guarded conversion script (re-verifies the diff; hard-stops on any unexpected maa-only path). Run inside a maa-framework checkout. |
| `HANDOFF-maa-framework-session.md` | Drop-in prompt for a Claude Code session scoped to maa-framework to execute the conversion + close #84 |

## Status

Analysis complete. Execution (PR + closing #84) must run from a maa-framework-scoped
session — this typed-wasm session lacks write access to that repo.
