#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-grade-kernel.sh — one definition of min-plus and one of max-plus.
#
# The grade kernel (src/abi/TypedWasm/ABI/ResourceAlgebra.idr and
# src/abi/TypedWasm/ABI/ResourceAlgebra/*.idr) is the only place in the tree
# allowed to define a grade algebra's operations.  Everything else draws its
# grades from it.  This gate fails on any tracked .idr file that:
#
#   R1  defines a structural min or max on Nat — a clause of the shape
#         f (S x) (S y) = S (f x y)
#       or a signature  <name containing min|max> : Nat -> Nat -> Nat.
#       No file may do this, kernel included: base's Data.Nat.minimum /
#       maximum are the one definition, used by the kernel.
#   R2  defines a grade operation outside the kernel — a clause that matches
#       two values of the same constructor and rebuilds that constructor from
#       a min, a max or a sum of their payloads:
#         op (C x) (C y) = C (minimum x y)  |  C (maximum x y)  |  C (x + y)
#       (any function name containing min/max counts as a min/max).
#
# A hit listed in tools/grade-kernel.allow (one "path<TAB>name<TAB>reason"
# per line) is reported as allowed, with its reason, instead of failing.
# The list is for operations that are provably neither min-plus nor
# max-plus; every entry must say which algebra it belongs to.
#
# Usage: tools/check-grade-kernel.sh             # gate the tree
#        tools/check-grade-kernel.sh --self-test # negative control: the
#                                                # gate must REJECT seeded
#                                                # duplicates and ACCEPT the
#                                                # kernel's own shapes
set -euo pipefail
cd "$(dirname "$0")/.."

KERNEL_RE='^src/abi/TypedWasm/ABI/ResourceAlgebra(\.idr|/[A-Za-z]+\.idr)$'
ALLOW_FILE="tools/grade-kernel.allow"

ID="[A-Za-z_][A-Za-z0-9_']*"
# A grade-carrier constructor: any capitalised name except Nat's own S (R1 covers S).
CON="[A-RT-Z][A-Za-z0-9_']*|S[A-Za-z0-9_']+"
WS="[[:space:]]"
# A min/max-like name: tropMin, natMax, minimum, maxNat, ... (but not maxMonoLTE).
MINMAX="[A-Za-z0-9_']*([Mm]in|[Mm]ax)(imum|Nat|N)?"
# R1a: f (S x) (S y) = S (f x y)   (backreference \1 = the function name)
R1A="^${WS}*(${ID})${WS}+\(S${WS}+${ID}\)${WS}+\(S${WS}+${ID}\)${WS}*=${WS}*S${WS}*\(${WS}*\1${WS}"
# R1b: <..min../..max..> : Nat -> Nat -> Nat
R1B="^${WS}*(private${WS}+|export${WS}+|public${WS}+export${WS}+)?${MINMAX}${WS}*:${WS}*Nat${WS}*->${WS}*Nat${WS}*->${WS}*Nat${WS}*$"
# R2: op (C x) (C y) = C (minlike x y | maxlike x y | x + y)
R2="^${WS}*(${ID})${WS}+\((${CON})${WS}+(${ID})\)${WS}+\(\2${WS}+(${ID})\)${WS}*=${WS}*\2${WS}*\((${MINMAX}${WS}+\3${WS}+\4|\3${WS}*\+${WS}*\4)${WS}*\)"

# scan FILE... — print "rule<TAB>file<TAB>line<TAB>name<TAB>text" per hit
scan() {
  local f
  for f in "$@"; do
    { grep -nE "$R1A" "$f" 2>/dev/null || true; } | while IFS=: read -r ln text; do
      name="$(printf '%s' "$text" | sed -E "s/^${WS}*(${ID}).*/\1/")"
      printf 'R1\t%s\t%s\t%s\t%s\n' "$f" "$ln" "$name" "$text"
    done
    { grep -nE "$R1B" "$f" 2>/dev/null || true; } | while IFS=: read -r ln text; do
      name="$(printf '%s' "$text" | sed -E "s/^${WS}*(private${WS}+|export${WS}+|public${WS}+export${WS}+)?(${ID}).*/\2/")"
      printf 'R1\t%s\t%s\t%s\t%s\n' "$f" "$ln" "$name" "$text"
    done
    if ! printf '%s\n' "$f" | grep -qE "$KERNEL_RE"; then
      { grep -nE "$R2" "$f" 2>/dev/null || true; } | while IFS=: read -r ln text; do
        name="$(printf '%s' "$text" | sed -E "s/^${WS}*(${ID}).*/\1/")"
        printf 'R2\t%s\t%s\t%s\t%s\n' "$f" "$ln" "$name" "$text"
      done
    fi
  done
}

# judge — read scan output on stdin; print verdicts; exit 1 on any non-allowed hit
judge() {
  local bad=0 rule f ln name text reason
  while IFS=$'\t' read -r rule f ln name text; do
    [ -z "$rule" ] && continue
    reason=""
    if [ -f "$ALLOW_FILE" ]; then
      reason="$(awk -F'\t' -v p="$f" -v n="$name" '$1==p && $2==n {print $3; exit}' "$ALLOW_FILE")"
    fi
    if [ -n "$reason" ]; then
      printf 'allowed %s %s:%s %s — %s\n' "$rule" "$f" "$ln" "$name" "$reason"
    else
      printf 'ERROR   %s %s:%s %s\n        %s\n' "$rule" "$f" "$ln" "$name" "$text"
      bad=1
    fi
  done
  return "$bad"
}

if [ "${1:-}" = "--self-test" ]; then
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/src/abi/TypedWasm/ABI/ResourceAlgebra"
  # Seeded duplicates — every one must be caught.
  cat > "$tmp/dup.idr" <<'EOF'
tropMin : Nat -> Nat -> Nat
tropMin Z     _     = Z
tropMin (S m) (S n) = S (tropMin m n)
private
natMax : Nat -> Nat -> Nat
natMax (S m) (S n) = S (natMax m n)
tropAdd (Finite a) (Finite b) = Finite (tropMin a b)
tropMul (Finite a) (Finite b) = Finite (a + b)
minNat : Nat -> Nat -> Nat
myMax (Val m) (Val n) = Val (maximum m n)
EOF
  # The kernel's own shapes — R2 must accept them inside the kernel path.
  cat > "$tmp/src/abi/TypedWasm/ABI/ResourceAlgebra/Loss.idr" <<'EOF'
lossSeq (Finite m) (Finite n) = Finite (m + n)
lossAlt (Finite m) (Finite n) = Finite (minimum m n)
EOF
  # Neighbours that are not min/max/plus definitions — must not be caught.
  cat > "$tmp/clean.idr" <<'EOF'
lte (S k) (S j) = lte k j
minimumCommutative (S k) (S j) = cong S $ minimumCommutative k j
tropMax (Finite a) Infinity = Infinity
pathBottleneck (x :: xs) = tropMax x (pathBottleneck xs)
maxMonoLTE (LTESucc p) (LTESucc q) = LTESucc (maxMonoLTE p q)
EOF
  dup_hits="$(cd "$tmp" && scan dup.idr | wc -l)"
  kern_hits="$(cd "$tmp" && scan src/abi/TypedWasm/ABI/ResourceAlgebra/Loss.idr | wc -l)"
  clean_hits="$(cd "$tmp" && scan clean.idr | wc -l)"
  status=0
  # dup.idr: 2 R1a clauses + 3 R1b signatures + 3 R2 clauses = 8
  if [ "$dup_hits" -eq 8 ]; then echo "PASS: seeded duplicates caught (8/8)"
  else echo "FAIL: seeded duplicates caught ${dup_hits}/8"; (cd "$tmp" && scan dup.idr); status=1; fi
  if [ "$kern_hits" -eq 0 ]; then echo "PASS: kernel's own grade operations accepted inside the kernel"
  else echo "FAIL: ${kern_hits} false hit(s) inside the kernel"; status=1; fi
  if [ "$clean_hits" -eq 0 ]; then echo "PASS: non-definitions not caught (0 false positives)"
  else echo "FAIL: ${clean_hits} false positive(s)"; (cd "$tmp" && scan clean.idr); status=1; fi
  exit "$status"
fi

# The positive half of "exactly one": inside the kernel, R2's shape must occur
# exactly twice in Loss.idr (lossSeq, lossAlt), exactly twice in MaxPlus.idr
# (maxPlusAlt, maxPlusSeq), and nowhere else.
kernel_count() { { grep -cE "$R2" "$1" 2>/dev/null || true; } | head -1; }
kernel_ok=1
for kf in $(git ls-files 'src/abi/TypedWasm/ABI/ResourceAlgebra.idr' 'src/abi/TypedWasm/ABI/ResourceAlgebra/*.idr'); do
  case "$kf" in
    */ResourceAlgebra/Loss.idr|*/ResourceAlgebra/MaxPlus.idr) want=2 ;;
    *) want=0 ;;
  esac
  got="$(kernel_count "$kf")"
  if [ "$got" -ne "$want" ]; then
    echo "ERROR   kernel ${kf}: ${got} grade-operation definition(s), expected ${want}"
    kernel_ok=0
  fi
done
for need in src/abi/TypedWasm/ABI/ResourceAlgebra/Loss.idr src/abi/TypedWasm/ABI/ResourceAlgebra/MaxPlus.idr; do
  git ls-files --error-unmatch "$need" >/dev/null 2>&1 || { echo "ERROR   kernel file missing: ${need}"; kernel_ok=0; }
done
[ "$kernel_ok" -eq 1 ] || { echo "GRADE-KERNEL GATE FAILED: the kernel does not hold exactly one min-plus and one max-plus."; exit 1; }

mapfile -t files < <(git ls-files '*.idr')
echo "grade-kernel gate: ${#files[@]} tracked .idr file(s); kernel = ${KERNEL_RE}"
if scan "${files[@]}" | judge; then
  echo "OK: one definition of min-plus (ResourceAlgebra/Loss.idr) and one of max-plus (ResourceAlgebra/MaxPlus.idr); no Nat min/max outside base"
else
  echo "GRADE-KERNEL GATE FAILED: a grade operation is defined outside the kernel (see CONTRACT.adoc / LEVEL-STATUS.adoc)."
  exit 1
fi
