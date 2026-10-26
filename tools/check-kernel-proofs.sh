#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-kernel-proofs.sh — the mechanical falsifiers behind the grade kernel.
#
#   1. upstream   resource-algebra's and occupancy-types' own checks, and
#                 choreographic-types' KCut slice, at the pins (Agda --safe
#                 --without-K --no-libraries --double-check + their rejects)
#   2. build      idris2 --build src/abi/typed-wasm.ipkg: exit 0 AND no
#                 `Error:` line (idris2 can exit 0 while printing an error)
#   3. rejects    every tests/reject/*.idr must FAIL, at its `invalid`
#                 declaration, with the message in its `-- EXPECT:` line, and
#                 not for a scoping/parsing/path reason
#   4. table      the Idris2 port, evaluated by tests/transcription/Explore.idr,
#                 must reproduce tests/transcription/ops.tsv exactly; the table
#                 must be accepted row by row by Agda `refl` against the PINNED
#                 Agda instances and by Idris2 `Refl` against the port
#   5. control    every row of tests/transcription/wrong-rows.tsv must be
#                 REFUSED by both provers
#
# A missing toolchain is a failure, never a skip.
#
# Usage: tools/check-kernel-proofs.sh           # check
#        tools/check-kernel-proofs.sh --regen   # rewrite ops.tsv from the port,
#                                               # then check (commit the diff)
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
ROOT="$(pwd)"
REGEN=0; [ "${1:-}" = "--regen" ] && REGEN=1

RA="_build/dependencies/resource-algebra"
OUT="_build/kernel-proofs"
TTC="$ROOT/src/abi/build/ttc"
AGDA_FLAGS=(--safe --without-K --no-libraries --double-check --ignore-interfaces)
WRONG_REASON='Undefined name|Couldn.t parse|Parse error|not in the source directory|Can.t find import|Module .* not found|INTERNAL ERROR|Not in scope|Failed to find'

fail=0
pass() { printf 'PASS: %s\n' "$1"; }
err()  { printf 'FAIL: %s\n' "$1"; fail=1; }
die()  { printf 'FAIL: %s\n' "$1"; exit 1; }

command -v idris2 >/dev/null || die "idris2 not on PATH (a gate that cannot run must not report OK)"
command -v agda   >/dev/null || die "agda not on PATH (a gate that cannot run must not report OK)"
iv="$(idris2 --version)"; av="$(agda --version | head -1)"
echo "$iv"; echo "$av"
case "$iv" in
  *"version 0.8.0"*) ;;
  *) [ -n "${ALLOW_ANY_IDRIS2:-}" ] || die "Idris2 0.8.0 required (src/abi targets 0.8.0; EXPECT messages are 0.8.0's). Set ALLOW_ANY_IDRIS2=1 to try another." ;;
esac
# The rejection checks match prover messages and locations, and both change
# between Agda releases: 2.8.0 prints `file:11.38` where 2.6.3 printed
# `file:11,38`, which occupancy-types' own reject check does not accept.
case "$av" in
  *"version 2.6.3"*) ;;
  *) [ -n "${ALLOW_ANY_AGDA:-}" ] || die "Agda 2.6.3 required (the pinned siblings' reject checks expect 2.6.3's messages). Set ALLOW_ANY_AGDA=1 to try another." ;;
esac
[ -d "$RA/src/ResourceAlgebra" ] || die "resource-algebra not fetched — run scripts/fetch-siblings.sh"
echo "resource-algebra at $(git -C "$RA" rev-parse HEAD)"
rm -rf "$OUT"; mkdir -p "$OUT"

# 1 — upstream at the pin -----------------------------------------------------
if (cd "$RA" && AGDA=agda bash scripts/check-agda.sh) > "$OUT/upstream.log" 2>&1; then
  pass "upstream: $(tail -1 "$OUT/upstream.log")"
else
  cat "$OUT/upstream.log"; err "upstream resource-algebra check failed at the pin"
fi
# occupancy-types (L13's reclamation law), checked against OUR resource-algebra
# pin: its own pin (b2c9f1f) predates Instances/MinMax and Morphism; this pin only
# adds modules and lemmas, so the check below is what shows nothing it uses moved.
OCC="_build/dependencies/occupancy-types"
[ -d "$OCC/src/OccupancyTypes" ] || die "occupancy-types not fetched — run scripts/fetch-siblings.sh"
echo "occupancy-types at $(git -C "$OCC" rev-parse HEAD)"
if (cd "$OCC" && AGDA=agda RESOURCE_ALGEBRA_SRC="$ROOT/$RA/src" bash scripts/check-agda.sh) > "$OUT/upstream-occupancy.log" 2>&1; then
  pass "upstream occupancy-types: $(tail -1 "$OUT/upstream-occupancy.log")"
else
  cat "$OUT/upstream-occupancy.log"; err "upstream occupancy-types check failed at the pin"
fi
# choreographic-types: only the K-CUT-LOSS slice KCut.idr ports (KCut.agda and
# its imports need resource-algebra alone; the rest of the repo also needs
# epistemic-types), plus the two side-condition rejects (K-7), each of which
# must be refused at its invalid declaration with upstream's "1 != 2".
CT="_build/dependencies/choreographic-types"
[ -d "$CT/src/Choreographic" ] || die "choreographic-types not fetched — run scripts/fetch-siblings.sh"
echo "choreographic-types at $(git -C "$CT" rev-parse HEAD)"
ct_flags=("${AGDA_FLAGS[@]}" -i "$RA/src" -i "$CT/src")
if agda "${ct_flags[@]}" "$CT/src/Choreographic/KCut.agda" > "$OUT/upstream-kcut.log" 2>&1; then
  pass "upstream choreographic-types: KCut.agda (K-1..K-5) checks against the resource-algebra pin"
else
  cat "$OUT/upstream-kcut.log"; err "upstream choreographic-types KCut.agda failed at the pin"
fi
for name in UnprojectableChoice InconsistentCut; do
  log="$OUT/upstream-reject-$name.log"
  if agda "${ct_flags[@]}" -i "$CT/tests/reject" "$CT/tests/reject/$name.agda" > "$log" 2>&1; then
    err "upstream reject $name ACCEPTED"
  elif grep -qE "$WRONG_REASON" "$log" || ! grep -q '1 != 2' "$log"; then
    cat "$log"; err "upstream reject $name refused for the wrong reason"
  else
    pass "upstream choreographic-types: rejected $name (1 != 2)"
  fi
done

# 2 — the ABI package ---------------------------------------------------------
# From clean, so a stale TTC cannot mask an error.
rm -rf src/abi/build
(cd src/abi && idris2 --build typed-wasm.ipkg) > "$OUT/build.log" 2>&1
st=$?
if [ "$st" -eq 0 ] && ! grep -q '^Error' "$OUT/build.log"; then
  pass "idris2 --build typed-wasm.ipkg: $(grep -c ': Building ' "$OUT/build.log") module(s) built, 0 errors"
else
  grep -A12 '^Error' "$OUT/build.log" | head -40; err "idris2 --build typed-wasm.ipkg (exit $st)"
fi
dangerous="$(grep -rnE '\b(believe_me|assert_total|assert_smaller|idris_crash)\b|%unsafe' \
  src/abi/TypedWasm/ABI/ResourceAlgebra.idr src/abi/TypedWasm/ABI/ResourceAlgebra/ \
  | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(--|\|\|\|)' || true)"
if [ -z "$dangerous" ]; then pass "kernel: zero believe_me / assert_total / assert_smaller / idris_crash"
else printf '%s\n' "$dangerous"; err "kernel contains a dangerous pattern"; fi

# 3 — expected rejections -----------------------------------------------------
n_rej=0
for f in tests/reject/*.idr; do
  [ -e "$f" ] || { err "no tests/reject/*.idr fixtures"; break; }
  n_rej=$((n_rej + 1))
  name="$(basename "$f" .idr)"
  expect="$(sed -n 's/^-- EXPECT: //p' "$f" | head -1)"
  decl="$(grep -nE '^invalid[[:space:]]*:' "$f" | head -1 | cut -d: -f1)"
  log="$OUT/reject-$name.log"
  (cd tests/reject && IDRIS2_PATH="$TTC" idris2 --build-dir "$ROOT/$OUT/reject-build" --check "$name.idr") > "$log" 2>&1
  loc="$(grep -oE "^${name}:[0-9]+:" "$log" | head -1 | cut -d: -f2)"
  if [ -z "$expect" ] || [ -z "$decl" ]; then
    err "reject $name: fixture lacks an '-- EXPECT:' line or an 'invalid :' declaration"
  elif ! grep -q '^Error' "$log"; then
    cat "$log"; err "reject $name: ACCEPTED — an invalid proof typechecked"
  elif grep -qE "$WRONG_REASON" "$log"; then
    cat "$log"; err "reject $name: refused for the WRONG reason (scope/parse/path), so the control proves nothing"
  elif [ -z "$loc" ] || [ "$loc" -lt "$decl" ]; then
    cat "$log"; err "reject $name: error not located at its invalid declaration (line ${decl})"
  elif ! grep -qE -- "$expect" "$log"; then
    cat "$log"; err "reject $name: refused, but not with the expected message: ${expect}"
  else
    pass "rejected $name at line ${loc} (${expect})"
  fi
done

# 4 — the transcription table -------------------------------------------------
(cd tests/transcription && IDRIS2_PATH="$TTC" idris2 --build-dir "$ROOT/$OUT/explore-build" --exec main Explore.idr) \
  > "$OUT/ops.explored.tsv" 2> "$OUT/explore.err"
if grep -qE 'Error|error' "$OUT/explore.err" || [ ! -s "$OUT/ops.explored.tsv" ]; then
  cat "$OUT/explore.err"; err "explorer did not run (tests/transcription/Explore.idr)"
else
  if [ "$REGEN" -eq 1 ]; then
    { sed -n '1,/^# resource-algebra @/p' tests/transcription/ops.tsv | grep '^#'
      cat "$OUT/ops.explored.tsv"; } > tests/transcription/ops.tsv.new
    mv tests/transcription/ops.tsv.new tests/transcription/ops.tsv
    echo "regenerated tests/transcription/ops.tsv ($(wc -l < "$OUT/ops.explored.tsv") rows)"
  fi
  if diff <(grep -v '^#' tests/transcription/ops.tsv) "$OUT/ops.explored.tsv" > "$OUT/table.diff"; then
    pass "explorer: the port reproduces ops.tsv ($(wc -l < "$OUT/ops.explored.tsv") rows)"
  else
    head -20 "$OUT/table.diff"
    err "the port no longer reproduces tests/transcription/ops.tsv — if the change is intended, run --regen and let Agda judge the new table"
  fi
fi

check_agda() { # check_agda DIR MODULE LOG
  agda "${AGDA_FLAGS[@]}" -i "$RA/src" -i "$1" "$1/$2.agda" > "$3" 2>&1
}
check_idris() { # check_idris DIR MODULE LOG — exit 0 and no Error line means accepted
  (cd "$1" && IDRIS2_PATH="$TTC" idris2 --build-dir "$ROOT/$OUT/tc-build" --check "$2.idr") > "$3" 2>&1
  local st=$?
  [ "$st" -eq 0 ] && ! grep -q '^Error' "$3"
}

bash tests/transcription/gen.sh tests/transcription/ops.tsv "$OUT/table" TranscriptionCheck 2> "$OUT/gen.log" \
  || { cat "$OUT/gen.log"; err "gen.sh failed on ops.tsv"; }
rows="$(grep -c '^row' "$OUT/table/TranscriptionCheck.agda" 2>/dev/null || echo 0)"
if check_agda "$OUT/table" TranscriptionCheck "$OUT/agda-table.log"; then
  pass "Agda (pinned resource-algebra) accepts the table by refl: $((rows / 2)) equalities"
else
  grep -B2 -A8 'TranscriptionCheck.agda:[0-9]' "$OUT/agda-table.log" | head -30
  err "Agda refuses the table: the port and the pinned Agda instances DISAGREE"
fi
if check_idris "$OUT/table" TranscriptionCheck "$OUT/idris-table.log"; then
  pass "Idris2 (port) accepts the table by Refl: $(grep -c '= Refl$' "$OUT/table/TranscriptionCheck.idr") equalities"
else
  grep -A10 '^Error' "$OUT/idris-table.log" | head -30; err "Idris2 refuses the table"
fi

# 5 — negative control: every wrong row refused by both -----------------------
i=0
while IFS= read -r line; do
  case "$line" in ''|'#'*) continue ;; esac
  i=$((i + 1)); m="WrongRow$i"; d="$OUT/wrong/$m"; mkdir -p "$d"
  printf '%s\n' "$line" > "$d/row.tsv"
  bash tests/transcription/gen.sh "$d/row.tsv" "$d" "$m" 2>/dev/null
  if check_agda "$d" "$m" "$d/agda.log"; then
    err "control: Agda ACCEPTED a wrong row: $(printf '%s' "$line" | tr '\t' ' ')"
  elif grep -qE "$WRONG_REASON" "$d/agda.log" || ! grep -q "$m.agda:[0-9]" "$d/agda.log"; then
    cat "$d/agda.log"; err "control: Agda refused $m for the wrong reason"
  else
    pass "control: Agda refuses $(printf '%s' "$line" | tr '\t' ' ')"
  fi
  if check_idris "$d" "$m" "$d/idris.log"; then
    err "control: Idris2 ACCEPTED a wrong row: $(printf '%s' "$line" | tr '\t' ' ')"
  elif grep -qE "$WRONG_REASON" "$d/idris.log" || ! grep -qE "^$m:[0-9]+:" "$d/idris.log"; then
    cat "$d/idris.log"; err "control: Idris2 refused $m for the wrong reason"
  else
    pass "control: Idris2 refuses $(printf '%s' "$line" | tr '\t' ' ')"
  fi
done < tests/transcription/wrong-rows.tsv
[ "$i" -gt 0 ] || err "control: tests/transcription/wrong-rows.tsv has no rows"

echo
if [ "$fail" -ne 0 ]; then echo "KERNEL PROOFS FAILED"; exit 1; fi
echo "OK: kernel proofs — build, ${n_rej} rejection(s), table, and ${i} negative control row(s)"
