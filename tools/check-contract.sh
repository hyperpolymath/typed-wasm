#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# check-contract.sh — the estate layering-contract gate (generic; identical in
# every repo). Enforces the inter-project invariants that keep
#   systemet <- anytype <- AffineScript -> typed-wasm <- ephapax
# composable, so independent work in one repo cannot silently DETACH it.
# Behaviour comes from contract.config.sh at the repo root. See CONTRACT.adoc.
#
#   I1  Dependency direction one-way          -> BLOCKING
#   I3  Shared ABI is a multi-producer contract -> BLOCKING (content-anchored)
#   I4  Role purity                           -> ADVISORY
#   Presence: CONTRACT.adoc + back-link       -> BLOCKING (presence)
#
# Usage: tools/check-contract.sh            # check
#        tools/check-contract.sh --reseal   # rewrite contract.abi.sha256
#                                            #   (ONLY with an abi_version bump + ADR)
set -uo pipefail
cd "$(dirname "$0")/.."
RESEAL=0; [ "${1:-}" = "--reseal" ] && RESEAL=1
RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; DIM=$'\033[2m'; RST=$'\033[0m'
fail=0; warn=0
err()  { printf '%sERROR%s   %s\n' "$RED" "$RST" "$1"; fail=1; }
note() { printf '%swarn%s    %s\n'  "$YEL" "$RST" "$1"; warn=$((warn+1)); }
ok()   { printf '%sok%s      %s\n'  "$GRN" "$RST" "$1"; }

[ -f contract.config.sh ] || { err "contract.config.sh missing"; exit 1; }
# shellcheck disable=SC1091
. ./contract.config.sh
: "${CONTRACT_ROLE:?contract.config.sh must set CONTRACT_ROLE}"
: "${CONTRACT_ABI_VERSION:=none}"
DIGEST_FILE="contract.abi.sha256"

# Presence
if [ -f CONTRACT.adoc ]; then ok "CONTRACT.adoc present (role: ${CONTRACT_ROLE})"
else err "CONTRACT.adoc missing — the rules for this repo are not written down"; fi
if grep -rql 'CONTRACT\.adoc' README* .claude/CLAUDE.md 2>/dev/null; then ok "back-link to CONTRACT.adoc present"
else note "no README/CLAUDE back-link to CONTRACT.adoc"; fi

# I1 — dependency direction (manifests + .gitmodules only; never prose)
i1=0
for name in ${CONTRACT_FORBIDDEN_DEPS:-}; do
  for m in ${CONTRACT_MANIFESTS:-} .gitmodules; do
    [ -f "$m" ] || continue
    if grep -nE "(hyperpolymath/${name}([./\"' ]|\$)|^[[:space:]]*\"?${name}\"?[[:space:]]*=)" "$m" \
         | grep -vE '^\s*#|SPDX' >/dev/null 2>&1; then
      err "I1 violation: '${name}' referenced as a dependency in ${m} (must not depend on downstream)"; i1=$((i1+1))
    fi
  done
done
[ "$i1" -eq 0 ] && ok "I1 dependency direction clean (forbidden deps: ${CONTRACT_FORBIDDEN_DEPS:-none})"

# I3 — shared-ABI drift (content-anchored regions)
extract_region() { awk -v m="$2" '
  $0 ~ (">>> CONTRACT-ABI-ANCHOR " m "($|[^A-Za-z0-9_-])") {on=1; next}
  $0 ~ ("<<< CONTRACT-ABI-ANCHOR " m "($|[^A-Za-z0-9_-])") {on=0}
  on {print}' "$1"; }
compute() { for a in ${CONTRACT_ABI_ANCHORS:-}; do
    f="${a%%::*}"; mk="${a##*::}"
    [ -f "$f" ] || { echo "MISSING  $a"; continue; }
    reg="$(extract_region "$f" "$mk")"
    [ -z "$reg" ] && { echo "NOMARKER $a"; continue; }
    printf '%s  %s\n' "$(printf '%s' "$reg" | sha256sum | cut -d' ' -f1)" "$a"
  done; }
if [ -n "${CONTRACT_ABI_ANCHORS:-}" ]; then
  if [ "$RESEAL" -eq 1 ]; then
    { echo "# ABI-anchor digests (abi_version=${CONTRACT_ABI_VERSION}). DO NOT hand-edit."
      echo "# Re-seal ONLY with an abi_version bump + an ADR. tools/check-contract.sh --reseal"
      compute; } > "$DIGEST_FILE"
    ok "re-sealed ${DIGEST_FILE} at abi_version=${CONTRACT_ABI_VERSION}"
  else
    [ -f "$DIGEST_FILE" ] || err "I3: ${DIGEST_FILE} missing — run tools/check-contract.sh --reseal"
    cur="$(compute)"
    if echo "$cur" | grep -qE '^(MISSING|NOMARKER)'; then
      echo "$cur" | grep -E '^(MISSING|NOMARKER)' | while read -r k a; do err "I3: anchor ${a}: ${k}"; done; fail=1
    fi
    exp="$(grep -vE '^\s*#' "$DIGEST_FILE" 2>/dev/null)"
    if [ "$(printf '%s' "$cur" | sort)" = "$(printf '%s' "$exp" | sort)" ]; then
      ok "I3 shared-ABI anchors unchanged (abi_version=${CONTRACT_ABI_VERSION})"
    else
      err "I3 violation: a shared-ABI anchor changed — this is a MULTI-PRODUCER ABI (${CONTRACT_FORBIDDEN_DEPS:-producers})."
      printf '        %sTo change it: bump CONTRACT_ABI_VERSION, reference a coordinated ADR, --reseal, update every producer.%s\n' "$DIM" "$RST"
      printf '        %sDo NOT re-seal to make this pass in isolation.%s\n' "$DIM" "$RST"
      diff <(printf '%s\n' "$exp"|sort) <(printf '%s\n' "$cur"|sort) | sed 's/^/          /' || true
    fi
  fi
else ok "I3 not applicable (no shared-ABI anchors for role ${CONTRACT_ROLE})"; fi

# I4 — role purity (advisory)
if [ -n "${CONTRACT_ROLE_DENY:-}" ]; then
  while IFS='|' read -r rx msg; do
    [ -z "$rx" ] && continue
    hits="$(grep -rInE "$rx" ${CONTRACT_SRC_DIRS:-src lib} 2>/dev/null | grep -vE 'CONTRACT|contract\.' | head -3)"
    [ -n "$hits" ] && { note "I4 (role purity): ${msg}"; printf '%s\n' "$hits" | sed 's/^/          /'; }
  done <<< "${CONTRACT_ROLE_DENY}"
else ok "I4 no role-purity denials declared"; fi

echo
if [ "$fail" -ne 0 ]; then
  printf '%sCONTRACT GATE FAILED%s — this change would detach the repo from the stack. See CONTRACT.adoc.\n' "$RED" "$RST"; exit 1; fi
printf '%sOK%s: contract gate — I1 + I3 hold%s\n' "$GRN" "$RST" "$([ "$warn" -gt 0 ] && echo " (${warn} advisory warning(s))")"
