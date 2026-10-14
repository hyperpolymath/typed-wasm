#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Fetch the sibling proof repositories at their pinned commits
# (pattern: residual-evidence-types / choreographic-types).
#
# typed-wasm consumes these by pin, never by re-declaring their definitions:
#   resource-algebra  — the grade kernel; src/abi/TypedWasm/ABI/ResourceAlgebra*
#                       is its Idris2 transcription, and tests/transcription
#                       checks the operation tables against this tree in Agda.
#   occupancy-types   — the reclamation law (R-1..R-6) that
#                       src/abi/TypedWasm/ABI/Occupancy.idr ports for L13.
#   choreographic-types — K-CUT-LOSS, which src/abi/TypedWasm/ABI/KCut.idr
#                       ports for L16.
#
# Re-pin deliberately, one commit per pin, and update the module headers that
# cite the pin in the same commit.  Override for a local experiment with
#   RESOURCE_ALGEBRA_COMMIT=<sha> OCCUPANCY_TYPES_COMMIT=<sha> \
#   CHOREOGRAPHIC_TYPES_COMMIT=<sha> scripts/fetch-siblings.sh
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

RESOURCE_ALGEBRA_COMMIT="${RESOURCE_ALGEBRA_COMMIT:-0b338c9fc45cd04e7ee7d00b3855cd59d56a2afe}"
OCCUPANCY_TYPES_COMMIT="${OCCUPANCY_TYPES_COMMIT:-af957280075699c659de0abd9a3b0defade77309}"
CHOREOGRAPHIC_TYPES_COMMIT="${CHOREOGRAPHIC_TYPES_COMMIT:-edb784a7d26c276c2abfa8399b773d346dbb101e}"

fetch() { # fetch <name> <commit>
  local name="$1" commit="$2" dir="_build/dependencies/$1"
  mkdir -p _build/dependencies
  if [ ! -d "$dir/.git" ]; then
    git clone --quiet "https://github.com/hyperpolymath/${name}.git" "$dir"
  fi
  if ! git -C "$dir" cat-file -e "${commit}^{commit}" 2>/dev/null; then
    git -C "$dir" fetch --quiet origin
  fi
  git -C "$dir" checkout --quiet --detach "$commit"
  local got
  got="$(git -C "$dir" rev-parse HEAD)"
  case "$got" in
    "$commit"*) echo "${name} at ${got}" ;;
    *) echo "ERROR: ${name} resolved to ${got}, expected ${commit}" >&2; exit 1 ;;
  esac
}

fetch resource-algebra "$RESOURCE_ALGEBRA_COMMIT"
fetch occupancy-types "$OCCUPANCY_TYPES_COMMIT"
fetch choreographic-types "$CHOREOGRAPHIC_TYPES_COMMIT"
