#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tests/e2e.sh — End-to-end structural validation for typed-wasm.
#
# Validates that:
#   1. Spec documents exist for all 12 type-safety levels
#   2. Example .twasm files cover levels 1-6 (checked core)
#   3. Idris2 ABI .idr files exist for all 10 checked levels
#   4. Zig FFI implementation files are present
#   5. ReScript parser source files are present
#   6. JSON/TOML/IPKG configuration files are well-formed
#   7. LEVEL-STATUS.md documents all 12 levels
#   8. Grammar document is non-trivial
#   9. SPDX licence headers are present on key files
#
# Usage:
#   bash tests/e2e.sh            # run all checks
#   E2E_BUILD=0 bash tests/e2e.sh  # skip build checks (structural only)

set -euo pipefail

# ---------------------------------------------------------------------------
# Colour helpers
# ---------------------------------------------------------------------------
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

PASSED=0
FAILED=0
SKIPPED=0

pass()   { echo -e "  ${GREEN}PASS${NC}  $*"; PASSED=$((PASSED + 1)); }
fail()   { echo -e "  ${RED}FAIL${NC}  $*"; FAILED=$((FAILED + 1)); }
skip()   { echo -e "  ${YELLOW}SKIP${NC}  $*"; SKIPPED=$((SKIPPED + 1)); }
section(){ echo -e "\n${CYAN}=== $* ===${NC}"; }

# ---------------------------------------------------------------------------
# Resolve project root
# ---------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_ROOT"

E2E_BUILD="${E2E_BUILD:-1}"

# ---------------------------------------------------------------------------
# 1. Spec documents
# ---------------------------------------------------------------------------
section "1. Spec documents"

# Main type-safety level spec document
if [ -f "spec/type-safety-levels-for-wasm.adoc" ]; then
  SIZE=$(wc -c < "spec/type-safety-levels-for-wasm.adoc")
  if [ "$SIZE" -gt 1000 ]; then
    pass "Level spec document exists and is non-trivial ($SIZE bytes)"
  else
    fail "Level spec document suspiciously small ($SIZE bytes)"
  fi
else
  fail "Missing: spec/type-safety-levels-for-wasm.adoc"
fi

# LEVEL-STATUS.md documents all 12 levels
if [ -f "LEVEL-STATUS.md" ]; then
  for lvl in $(seq 1 12); do
    if grep -q "| $lvl |" "LEVEL-STATUS.md" 2>/dev/null; then
      pass "LEVEL-STATUS.md contains level $lvl"
    else
      fail "LEVEL-STATUS.md missing entry for level $lvl"
    fi
  done
else
  fail "Missing: LEVEL-STATUS.md"
fi

# Grammar document
if [ -f "spec/grammar.ebnf" ]; then
  SIZE=$(wc -c < "spec/grammar.ebnf")
  if [ "$SIZE" -gt 100 ]; then
    pass "Grammar spec exists ($SIZE bytes)"
  else
    fail "Grammar spec suspiciously small ($SIZE bytes): spec/grammar.ebnf"
  fi
else
  fail "Missing: spec/grammar.ebnf"
fi

# ---------------------------------------------------------------------------
# 2. Example .twasm files (levels 1-6 checked core)
# ---------------------------------------------------------------------------
section "2. Example .twasm files (levels 1-6)"

EXPECTED_EXAMPLES=(
  "examples/01-single-module.twasm"
  "examples/02-multi-module.twasm"
  "examples/03-ownership-linearity.twasm"
  "examples/04-ecs-game.twasm"
)

for f in "${EXPECTED_EXAMPLES[@]}"; do
  if [ -f "$f" ]; then
    SIZE=$(wc -c < "$f")
    if [ "$SIZE" -gt 0 ]; then
      pass "Example file exists and is non-empty: $f"
    else
      fail "Empty example file: $f"
    fi
  else
    fail "Missing example file: $f"
  fi
done

# Total .twasm count
TWASM_COUNT=$(find examples -name "*.twasm" | wc -l)
if [ "$TWASM_COUNT" -ge 4 ]; then
  pass "examples/ contains $TWASM_COUNT .twasm files (>= 4)"
else
  fail "Too few .twasm examples: $TWASM_COUNT (expected >= 4)"
fi

# ---------------------------------------------------------------------------
# 3. Idris2 ABI files — all 10 checked levels (L1-L10)
# ---------------------------------------------------------------------------
section "3. Idris2 ABI files (L1-L10)"

ABI_DIR="src/abi/TypedWasm/ABI"

IDR_FILES=(
  "$ABI_DIR/Region.idr"
  "$ABI_DIR/TypedAccess.idr"
  "$ABI_DIR/Pointer.idr"
  "$ABI_DIR/Levels.idr"
  "$ABI_DIR/Effects.idr"
  "$ABI_DIR/Lifetime.idr"
  "$ABI_DIR/Linear.idr"
  "$ABI_DIR/Proofs.idr"
  "$ABI_DIR/MultiModule.idr"
)

for f in "${IDR_FILES[@]}"; do
  if [ -f "$f" ]; then
    SIZE=$(wc -c < "$f")
    if [ "$SIZE" -gt 50 ]; then
      pass "Idris2 ABI file exists: $f ($SIZE bytes)"
    else
      fail "Idris2 ABI file is trivially small: $f ($SIZE bytes)"
    fi
  else
    fail "Missing Idris2 ABI file: $f"
  fi
done

# Draft-only files (L11, L12 — must exist but may be minimal)
DRAFT_IDR_FILES=(
  "$ABI_DIR/Tropical.idr"
  "$ABI_DIR/Epistemic.idr"
)

for f in "${DRAFT_IDR_FILES[@]}"; do
  if [ -f "$f" ]; then
    pass "Draft Idris2 file exists (L11/L12): $f"
  else
    fail "Missing draft Idris2 file: $f"
  fi
done

# ---------------------------------------------------------------------------
# 4. Zig FFI implementation
# ---------------------------------------------------------------------------
section "4. Zig FFI implementation"

ZIG_FILES=(
  "ffi/zig/build.zig"
  "ffi/zig/src/main.zig"
)

for f in "${ZIG_FILES[@]}"; do
  if [ -f "$f" ]; then
    SIZE=$(wc -c < "$f")
    pass "Zig FFI file exists: $f ($SIZE bytes)"
  else
    fail "Missing Zig FFI file: $f"
  fi
done

# ---------------------------------------------------------------------------
# 5. ReScript parser source files
# ---------------------------------------------------------------------------
section "5. ReScript parser source files"

PARSER_FILES=(
  "src/parser/Parser.res"
  "src/parser/Lexer.res"
  "src/parser/Ast.res"
  "src/parser/Parser.mjs"
  "src/parser/Lexer.mjs"
  "src/parser/Ast.mjs"
)

for f in "${PARSER_FILES[@]}"; do
  if [ -f "$f" ]; then
    pass "Parser file exists: $f"
  else
    fail "Missing parser file: $f"
  fi
done

# ---------------------------------------------------------------------------
# 6. Configuration files are well-formed
# ---------------------------------------------------------------------------
section "6. Configuration file integrity"

# typed-wasm.ipkg (Idris2 package — lives under src/abi/)
IPKG_FILE="src/abi/typed-wasm.ipkg"
if [ -f "$IPKG_FILE" ]; then
  if grep -q "^package " "$IPKG_FILE" 2>/dev/null; then
    pass "$IPKG_FILE has package declaration"
  else
    fail "$IPKG_FILE missing package declaration"
  fi
else
  fail "Missing Idris2 package file: $IPKG_FILE"
fi

# selur-compose.toml (Stapeln/container config)
if [ -f "selur-compose.toml" ]; then
  if grep -q "\[" "selur-compose.toml" 2>/dev/null; then
    pass "selur-compose.toml has TOML sections"
  else
    fail "selur-compose.toml appears malformed"
  fi
else
  skip "selur-compose.toml not present (optional)"
fi

# deno.lock or package.json for JS deps
if [ -f "deno.lock" ]; then
  pass "deno.lock present (Deno dependency lockfile)"
elif [ -f "package.json" ]; then
  pass "package.json present (JS deps)"
else
  skip "No JS lockfile found (deno.lock / package.json)"
fi

# ---------------------------------------------------------------------------
# 7. Required structural files
# ---------------------------------------------------------------------------
section "7. Required structural files (RSR)"

RSR_FILES=(
  "README.adoc"
  "EXPLAINME.adoc"
  "SECURITY.md"
  "CONTRIBUTING.adoc"
  "LICENSE"
  "Justfile"
  "0-AI-MANIFEST.a2ml"
)

for f in "${RSR_FILES[@]}"; do
  if [ -f "$f" ]; then
    pass "RSR file present: $f"
  else
    fail "Missing RSR file: $f"
  fi
done

# ---------------------------------------------------------------------------
# 8. SPDX licence headers on key source files
# ---------------------------------------------------------------------------
section "8. SPDX licence headers"

SPDX_CHECK_FILES=(
  "src/parser/Parser.res"
  "src/parser/Lexer.res"
  "ffi/zig/src/main.zig"
  "tests/e2e/e2e-smoke.mjs"
)

for f in "${SPDX_CHECK_FILES[@]}"; do
  if [ -f "$f" ]; then
    if grep -q "SPDX-License-Identifier" "$f" 2>/dev/null; then
      pass "SPDX header present: $f"
    else
      fail "Missing SPDX-License-Identifier in: $f"
    fi
  else
    skip "File not found (cannot check SPDX): $f"
  fi
done

# ---------------------------------------------------------------------------
# 9. Existing smoke test can be invoked (node available)
# ---------------------------------------------------------------------------
section "9. Smoke test invocability"

if command -v node &>/dev/null; then
  echo "  Invoking: node tests/e2e/e2e-smoke.mjs"
  if node tests/e2e/e2e-smoke.mjs 2>&1 | tail -5; then
    if node tests/e2e/e2e-smoke.mjs 2>&1 | grep -q "passed"; then
      pass "Smoke test ran and reports passed"
    else
      fail "Smoke test ran but reported failures or no 'passed' summary"
    fi
  else
    fail "Smoke test exited with non-zero status"
  fi
else
  skip "node not found — skipping smoke test invocation"
fi

# ---------------------------------------------------------------------------
# 10. Build check (optional — skip with E2E_BUILD=0)
# ---------------------------------------------------------------------------
section "10. Build check"

if [ "$E2E_BUILD" = "0" ]; then
  skip "Build check skipped (E2E_BUILD=0)"
else
  if command -v idris2 &>/dev/null; then
    echo "  Running: idris2 --build src/abi/typed-wasm.ipkg"
    if (cd src/abi && idris2 --build typed-wasm.ipkg 2>&1 | tail -5); then
      pass "idris2 build succeeded"
    else
      fail "idris2 build failed"
    fi
  else
    skip "idris2 not found — skipping Idris2 build check"
  fi

  if command -v zig &>/dev/null; then
    echo "  Running: zig build (ffi/zig/)"
    if (cd ffi/zig && zig build 2>&1 | tail -5); then
      pass "zig build succeeded"
    else
      fail "zig build failed"
    fi
  else
    skip "zig not found — skipping Zig FFI build check"
  fi
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=============================="
echo " E2E Results: ${PASSED} passed, ${FAILED} failed, ${SKIPPED} skipped"
echo "=============================="

if [ "$FAILED" -gt 0 ]; then
  echo -e "${RED}E2E validation FAILED with $FAILED error(s)${NC}"
  exit 1
else
  echo -e "${GREEN}E2E validation PASSED${NC}"
  exit 0
fi
