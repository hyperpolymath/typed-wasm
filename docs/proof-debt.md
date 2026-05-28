<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
-->

# Proof Debt — typed-wasm

**Schema**: [hyperpolymath/standards `TRUSTED-BASE-REDUCTION-POLICY.adoc`](https://github.com/hyperpolymath/standards/blob/main/docs/TRUSTED-BASE-REDUCTION-POLICY.adoc) (standards#203).

## Current state

**Zero soundness-relevant escape hatches** in this repo as of 2026-05-26.

Verified by `scripts/check-trusted-base.sh` from
[hyperpolymath/standards](https://github.com/hyperpolymath/standards) —
all matches found by syntactic scan were inside docstrings explicitly
stating the file does NOT use `believe_me` / `assert_total` /
`postulate` / `sorry` / `Admitted` (the "no escape hatches"
discipline pattern).

## (a) DISCHARGED in this repo

*(None — never any to discharge.)*

## (b) BUDGETED — tested with a refutation budget

*(None.)*

## (c) NECESSARY AXIOM

*(None.)*

## (d) DEBT — actively to be closed

*(None.)*

## Preservation contract

This file exists to assert the **zero-debt invariant** for the
`scripts/check-trusted-base.sh` CI gate (standards#211). Any future PR
that introduces a soundness-relevant escape hatch MUST either:

1. annotate the call site with a leading `TRUSTED:` / `AXIOM:`
   comment, OR
2. add an entry to this file under §(b) / §(c) / §(d).

PRs that introduce un-annotated escape hatches will fail CI.

## Companion documents

- [standards#195](https://github.com/hyperpolymath/standards/pull/195) — estate proof-debt audit.
- [standards#203](https://github.com/hyperpolymath/standards/pull/203) — trusted-base reduction policy (the schema this file follows).
- [standards#211](https://github.com/hyperpolymath/standards/pull/211) — `check-trusted-base.sh` CI enforcement.

---

🤖 Initial seed by Claude Code, 2026-05-26.
