# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Project automation for typed-wasm.
#
# Run `just` to see all available recipes
# Run `just cookbook` to generate docs/just-cookbook.adoc
# Run `just combinations` to see matrix recipe options

set shell := ["bash", "-uc"]
set dotenv-load := true
set positional-arguments := true

# Import auto-generated contractile recipes (must-check, trust-verify, etc.)
# Re-generate with: contractile gen-just
import? "contractile.just"

# Project metadata — customize these
project := "typed-wasm"
OWNER := "hyperpolymath"
REPO := "typed-wasm"
version := "0.1.0"
tier := "infrastructure"  # 1 | 2 | infrastructure

# ═══════════════════════════════════════════════════════════════════════════════
# DEFAULT & HELP
# ═══════════════════════════════════════════════════════════════════════════════

# Show all available recipes with descriptions
default:
    @just --list --unsorted

# Show detailed help for a specific recipe
help recipe="":
    #!/usr/bin/env bash
    if [ -z "{{recipe}}" ]; then
        just --list --unsorted
        echo ""
        echo "Usage: just help <recipe>"
        echo "       just cookbook     # Generate full documentation"
        echo "       just combinations # Show matrix recipes"
    else
        just --show "{{recipe}}" 2>/dev/null || echo "Recipe '{{recipe}}' not found"
    fi

# Show this project's info
info:
    @echo "Project: {{project}}"
    @echo "Version: {{version}}"
    @echo "RSR Tier: {{tier}}"
    @echo "Recipes: $(just --summary | wc -w)"
    @[ -f ".machine_readable/STATE.a2ml" ] && grep -oP 'phase\s*=\s*"\K[^"]+' .machine_readable/STATE.a2ml | head -1 | xargs -I{} echo "Phase: {}" || true

# Repository is already instantiated; there is no template bootstrap step.
init:
    @echo "typed-wasm is already instantiated; there is no template bootstrap step."

# ═══════════════════════════════════════════════════════════════════════════════
# BUILD & COMPILE
# ═══════════════════════════════════════════════════════════════════════════════

# Build the project — ReScript parser + Zig FFI
build *args:
    @echo "Building {{project}}..."
    rescript build
    cd ffi/zig && zig build
    @echo "Build complete"

# Build in release mode with optimizations
build-release *args:
    @echo "Building {{project}} (release)..."
    rescript build
    cd ffi/zig && zig build -Doptimize=ReleaseFast
    @echo "Release build complete"

# Build and watch for changes
build-watch:
    @echo "Watching for changes..."
    find src -name '*.res' | entr -c just build

# Clean build artifacts [reversible: rebuild with `just build`]
clean:
    @echo "Cleaning..."
    rescript clean
    rm -rf lib/bs lib/ocaml
    rm -rf ffi/zig/zig-out ffi/zig/.zig-cache
    rm -rf src/abi/build

# Deep clean including caches [reversible: rebuild]
clean-all: clean
    rm -rf .cache .tmp node_modules

# ═══════════════════════════════════════════════════════════════════════════════
# TEST & QUALITY
# ═══════════════════════════════════════════════════════════════════════════════

# Run all tests — ReScript parser tests + Zig FFI tests
test *args:
    @echo "Running ReScript parser tests..."
    rescript build
    node tests/parser/ParserTests.mjs
    @echo ""
    @echo "Running contract tests..."
    node tests/contracts/airborne-step-state-contract.mjs
    @echo ""
    @echo "Running Zig FFI tests..."
    cd ffi/zig && zig build test
    @echo ""
    @echo "All tests passed!"

# Run tests with verbose output
test-verbose:
    @echo "Running all tests (verbose)..."
    rescript build
    node tests/parser/ParserTests.mjs
    cd ffi/zig && zig build test
    node tests/smoke/e2e-smoke.mjs

# End-to-end smoke test — parse example, verify ABI correspondence
test-smoke:
    @echo "Running E2E smoke test..."
    rescript build
    node tests/smoke/e2e-smoke.mjs

# ABI contract tests
test-contract:
    @echo "Running ABI contract tests..."
    node tests/contracts/airborne-step-state-contract.mjs

# End-to-end test surface
test-e2e:
    @echo "Running end-to-end tests..."
    rescript build
    node tests/e2e/e2e-smoke.mjs

# Aspect tests for cross-surface claim coherence
test-aspect:
    @echo "Running aspect tests..."
    node tests/aspect/claim-envelope.mjs

# Parser benchmark surface
bench:
    @echo "Running parser benchmark..."
    rescript build
    node benchmarks/parser-bench.mjs

# Type-check Idris2 ABI modules (formal proofs)
check-abi:
    @echo "Type-checking Idris2 ABI modules..."
    cd src/abi && idris2 --build typed-wasm.ipkg
    @echo "Checked ABI package type-checks successfully."

# Run all quality checks
quality: fmt-check lint test test-e2e test-aspect
    @echo "All quality checks passed!"

# Fix all auto-fixable issues [reversible: git checkout]
fix: fmt
    @echo "Fixed all auto-fixable issues"

# ═══════════════════════════════════════════════════════════════════════════════
# LINT & FORMAT
# ═══════════════════════════════════════════════════════════════════════════════

# Format all source files [reversible: git checkout]
fmt:
    @echo "Formatting source files..."
    npx rescript format
    zig fmt ffi/zig/build.zig ffi/zig/src/main.zig ffi/zig/test/integration_test.zig ffi/zig/test/echidna_oracle_test.zig >/dev/null

# Check formatting without changes
fmt-check:
    @echo "Checking formatting..."
    npx rescript format --check
    zig fmt --check ffi/zig/build.zig ffi/zig/src/main.zig ffi/zig/test/integration_test.zig ffi/zig/test/echidna_oracle_test.zig

# Run linter
lint:
    @echo "Linting ReScript sources with warnings-as-errors..."
    npx rescript build --warn-error "+3+4+45+102"

# ═══════════════════════════════════════════════════════════════════════════════
# RUN & EXECUTE
# ═══════════════════════════════════════════════════════════════════════════════

# Run the application
run *args: build
    node tests/smoke/e2e-smoke.mjs

# Run with verbose output
run-verbose *args: build
    just test-verbose

# Install to user path
install: build-release
    @mkdir -p .local/bin
    @cp tests/smoke/e2e-smoke.mjs .local/bin/typed-wasm-smoke.mjs
    @echo "Staged .local/bin/typed-wasm-smoke.mjs for local execution"

# ═══════════════════════════════════════════════════════════════════════════════
# DEPENDENCIES
# ═══════════════════════════════════════════════════════════════════════════════

# Install/check all dependencies
deps:
    @echo "Checking dependencies..."
    @command -v node >/dev/null
    @command -v npx >/dev/null
    @command -v zig >/dev/null
    @command -v idris2 >/dev/null
    @test -d node_modules || npm ci
    @npm ls >/dev/null
    @echo "All dependencies satisfied"

# Audit dependencies for vulnerabilities
deps-audit:
    @echo "Auditing for vulnerabilities..."
    @npm audit --omit=dev --audit-level=high
    @command -v trivy >/dev/null && trivy fs --severity HIGH,CRITICAL --quiet . || true
    @command -v gitleaks >/dev/null && gitleaks detect --source . --no-git --quiet || true
    @echo "Audit complete"

# ═══════════════════════════════════════════════════════════════════════════════
# DOCUMENTATION
# ═══════════════════════════════════════════════════════════════════════════════

# Generate all documentation
docs:
    @mkdir -p docs/generated docs/man
    just cookbook
    just man
    @echo "Documentation generated in docs/"

# Generate justfile cookbook documentation
cookbook:
    #!/usr/bin/env bash
    mkdir -p docs
    OUTPUT="docs/just-cookbook.adoc"
    echo "= {{project}} Justfile Cookbook" > "$OUTPUT"
    echo ":toc: left" >> "$OUTPUT"
    echo ":toclevels: 3" >> "$OUTPUT"
    echo "" >> "$OUTPUT"
    echo "Generated: $(date -Iseconds)" >> "$OUTPUT"
    echo "" >> "$OUTPUT"
    echo "== Recipes" >> "$OUTPUT"
    echo "" >> "$OUTPUT"
    just --list --unsorted | while read -r line; do
        if [[ "$line" =~ ^[[:space:]]+([a-z_-]+) ]]; then
            recipe="${BASH_REMATCH[1]}"
            echo "=== $recipe" >> "$OUTPUT"
            echo "" >> "$OUTPUT"
            echo "[source,bash]" >> "$OUTPUT"
            echo "----" >> "$OUTPUT"
            echo "just $recipe" >> "$OUTPUT"
            echo "----" >> "$OUTPUT"
            echo "" >> "$OUTPUT"
        fi
    done
    echo "Generated: $OUTPUT"

# Generate man page
man:
    #!/usr/bin/env bash
    mkdir -p docs/man
    cat > docs/man/{{project}}.1 << EOF
    .TH {{project}} 1 "$(date +%Y-%m-%d)" "{{version}}" "{{project}} Manual"
    .SH NAME
    {{project}} \- RSR-compliant project
    .SH SYNOPSIS
    .B just
    [recipe] [args...]
    .SH DESCRIPTION
    RSR (Rhodium Standard Repository) project managed with just.
    .SH AUTHOR
    $(git config user.name 2>/dev/null || echo "Author") <$(git config user.email 2>/dev/null || echo "email")>
    EOF
    echo "Generated: docs/man/{{project}}.1"

# ═══════════════════════════════════════════════════════════════════════════════
# CI & AUTOMATION
# ═══════════════════════════════════════════════════════════════════════════════

# Run full CI pipeline locally
ci: deps quality
    @echo "CI pipeline complete!"

# Install git hooks
install-hooks:
    @mkdir -p .git/hooks
    @cat > .git/hooks/pre-commit << 'HOOKEOF'
    #!/bin/bash
    just fmt-check || exit 1
    just lint || exit 1
    just assail || exit 1
    HOOKEOF
    @chmod +x .git/hooks/pre-commit
    @echo "Git hooks installed"

# ═══════════════════════════════════════════════════════════════════════════════
# SECURITY
# ═══════════════════════════════════════════════════════════════════════════════

# Run security audit
security: deps-audit
    @echo "=== Security Audit ==="
    @command -v gitleaks >/dev/null && gitleaks detect --source . --verbose || true
    @command -v trivy >/dev/null && trivy fs --severity HIGH,CRITICAL . || true
    @echo "Security audit complete"

# Generate SBOM
sbom:
    @mkdir -p docs/security
    @command -v syft >/dev/null && syft . -o spdx-json > docs/security/sbom.spdx.json || echo "syft not found"

# ═══════════════════════════════════════════════════════════════════════════════
# VALIDATION & COMPLIANCE
# ═══════════════════════════════════════════════════════════════════════════════

# Validate RSR compliance
validate-rsr:
    #!/usr/bin/env bash
    echo "=== RSR Compliance Check ==="
    MISSING=""
    for f in .editorconfig .gitignore Justfile README.adoc LICENSE 0-AI-MANIFEST.a2ml; do
        [ -f "$f" ] || MISSING="$MISSING $f"
    done
    for f in .machine_readable/STATE.a2ml .machine_readable/META.a2ml .machine_readable/ECOSYSTEM.a2ml .machine_readable/anchors/ANCHOR.a2ml .machine_readable/policies/MAINTENANCE-AXES.a2ml .machine_readable/policies/MAINTENANCE-CHECKLIST.a2ml .machine_readable/policies/SOFTWARE-DEVELOPMENT-APPROACH.a2ml; do
        [ -f "$f" ] || MISSING="$MISSING $f"
    done
    for f in licensing/exhibits/EXHIBIT-A-ETHICAL-USE.txt licensing/exhibits/EXHIBIT-B-QUANTUM-SAFE.txt licensing/texts/PMPL-1.0-or-later.txt; do
        [ -f "$f" ] || MISSING="$MISSING $f"
    done
    for f in src/interface/abi src/interface/generated ffi/zig; do
        [ -d "$f" ] || MISSING="$MISSING $f"
    done
    for f in docs/maintenance/MAINTENANCE-CHECKLIST.adoc docs/practice/SOFTWARE-DEVELOPMENT-APPROACH.adoc; do
        [ -f "$f" ] || MISSING="$MISSING $f"
    done
    if [ -f ".machine_readable/META.a2ml" ]; then
        grep -q 'axis-1 = "must > intend > like"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:axis-1"
        grep -q 'axis-2 = "corrective > adaptive > perfective"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:axis-2"
        grep -q 'axis-3 = "systems > compliance > effects"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:axis-3"
        grep -q 'scoping-first = true' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:scoping-first"
        grep -q 'idris-unsound-scan = "believe_me/assert_total"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:idris-unsound-scan"
        grep -q 'audit-focus = "systems in place, documentation explains actual state, safety/security accounted for, observed effects reviewed"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:audit-focus"
        grep -q 'compliance-focus = "seams/compromises/exception register, bounded exceptions, anti-drift checks"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:compliance-focus"
        grep -q 'effects-evidence = "benchmark execution/results and maintainer status dialogue/review"' .machine_readable/META.a2ml || MISSING="$MISSING META.a2ml:effects-evidence"
        grep -q 'compliance-tooling = "panic-attack"' .machine_readable/policies/MAINTENANCE-AXES.a2ml || MISSING="$MISSING MAINTENANCE-AXES.a2ml:compliance-tooling"
        grep -q 'effects-tooling = "ecological checking with sustainabot guidance"' .machine_readable/policies/MAINTENANCE-AXES.a2ml || MISSING="$MISSING MAINTENANCE-AXES.a2ml:effects-tooling"
        grep -q 'source-human = "docs/maintenance/MAINTENANCE-CHECKLIST.adoc"' .machine_readable/policies/MAINTENANCE-CHECKLIST.a2ml || MISSING="$MISSING MAINTENANCE-CHECKLIST.a2ml:source-human"
        grep -q 'source-human = "docs/practice/SOFTWARE-DEVELOPMENT-APPROACH.adoc"' .machine_readable/policies/SOFTWARE-DEVELOPMENT-APPROACH.a2ml || MISSING="$MISSING SOFTWARE-DEVELOPMENT-APPROACH.a2ml:source-human"
    fi
    if [ -n "$MISSING" ]; then
        echo "MISSING:$MISSING"
        exit 1
    fi
    echo "RSR compliance: PASS"

# Validate STATE.a2ml syntax
validate-state:
    @if [ -f ".machine_readable/STATE.a2ml" ]; then \
        grep -q '^\[metadata\]' .machine_readable/STATE.a2ml && \
        grep -q 'project\s*=' .machine_readable/STATE.a2ml && \
        echo "STATE.a2ml: valid" || echo "STATE.a2ml: INVALID (missing required sections)"; \
    else \
        echo "No .machine_readable/STATE.a2ml found"; \
    fi

# Validate AI installation guide completeness (finishbot pre-release check)
validate-ai-install:
    #!/usr/bin/env bash
    echo "=== AI Installation Guide Check ==="
    GUIDE="docs/AI_INSTALLATION_GUIDE.adoc"
    README="README.adoc"
    ERRORS=0

    # Check guide exists
    if [ ! -f "$GUIDE" ]; then
        echo "MISSING: $GUIDE (create from template: docs/AI_INSTALLATION_GUIDE.adoc)"
        ERRORS=$((ERRORS + 1))
    else
        # Check for unfilled install markers
        INSTALL_MARKER='[TO''DO-AI-INSTALL]'
        TODOS=$(grep -cF "$INSTALL_MARKER" "$GUIDE" 2>/dev/null || true)
        if [ "$TODOS" -gt 0 ]; then
            echo "INCOMPLETE: $GUIDE has $TODOS unfilled AI install markers:"
            grep -nF "$INSTALL_MARKER" "$GUIDE" | head -10
            ERRORS=$((ERRORS + 1))
        else
            echo "$GUIDE: complete (no install markers)"
        fi

        # Check AI implementation section exists
        if ! grep -q 'ai-implementation' "$GUIDE" 2>/dev/null; then
            echo "MISSING: [[ai-implementation]] anchor in $GUIDE"
            ERRORS=$((ERRORS + 1))
        fi

        # Check privacy notice exists
        if ! grep -qi 'privacy' "$GUIDE" 2>/dev/null; then
            echo "MISSING: Privacy notice in $GUIDE"
            ERRORS=$((ERRORS + 1))
        fi

        # Check install commands exist (not just placeholders)
        if ! grep -q 'git clone' "$GUIDE" 2>/dev/null; then
            echo "WARNING: No git clone command found in $GUIDE -- install commands may be incomplete"
        fi
    fi

    # Check README has AI install section
    if [ -f "$README" ]; then
        if ! grep -qi 'AI-Assisted Installation' "$README" 2>/dev/null; then
            echo "MISSING: AI-Assisted Installation section in $README"
            echo "  Copy from docs/AI-INSTALL-README-SECTION.adoc"
            ERRORS=$((ERRORS + 1))
        fi

        # Check README for unfilled install markers
        INSTALL_MARKER='[TO''DO-AI-INSTALL]'
        README_TODOS=$(grep -cF "$INSTALL_MARKER" "$README" 2>/dev/null || true)
        if [ "$README_TODOS" -gt 0 ]; then
            echo "INCOMPLETE: $README has $README_TODOS unfilled AI install markers"
            ERRORS=$((ERRORS + 1))
        fi
    fi

    if [ "$ERRORS" -gt 0 ]; then
        echo ""
        echo "AI install guide: FAIL ($ERRORS issues)"
        exit 1
    fi
    echo "AI install guide: PASS"

# Full validation suite
validate: validate-rsr validate-state validate-ai-install
    @echo "All validations passed!"

# ═══════════════════════════════════════════════════════════════════════════════
# STATE MANAGEMENT
# ═══════════════════════════════════════════════════════════════════════════════

# Update STATE.a2ml timestamp
state-touch:
    @if [ -f ".machine_readable/STATE.a2ml" ]; then \
        sed -i 's/last-updated = "[^"]*"/last-updated = "'"$(date +%Y-%m-%d)"'"/' .machine_readable/STATE.a2ml && \
        echo "STATE.a2ml timestamp updated"; \
    fi

# Show current phase from STATE.a2ml
state-phase:
    @grep -oP 'phase\s*=\s*"\K[^"]+' .machine_readable/STATE.a2ml 2>/dev/null | head -1 || echo "unknown"

# ═══════════════════════════════════════════════════════════════════════════════
# GUIX & NIX
# ═══════════════════════════════════════════════════════════════════════════════

# Enter Guix development shell (primary)
guix-shell:
    guix shell -D -f guix.scm

# Build with Guix
guix-build:
    guix build -f guix.scm

# Enter Nix development shell (fallback)
nix-shell:
    @if [ -f "flake.nix" ]; then nix develop; else echo "No flake.nix"; fi

# ═══════════════════════════════════════════════════════════════════════════════
# HYBRID AUTOMATION
# ═══════════════════════════════════════════════════════════════════════════════

# Run local automation tasks
automate task="all":
    #!/usr/bin/env bash
    case "{{task}}" in
        all) just fmt && just lint && just test && just docs && just state-touch ;;
        cleanup) just clean && find . -name "*.orig" -delete && find . -name "*~" -delete ;;
        update) just deps && just validate ;;
        *) echo "Unknown: {{task}}. Use: all, cleanup, update" && exit 1 ;;
    esac

# ═══════════════════════════════════════════════════════════════════════════════
# COMBINATORIC MATRIX RECIPES
# ═══════════════════════════════════════════════════════════════════════════════

# Build matrix: [debug|release] x [target] x [features]
build-matrix mode="debug" target="" features="":
    @echo "Build matrix: mode={{mode}} target={{target}} features={{features}}"

# Test matrix: [unit|integration|e2e|all] x [verbosity] x [parallel]
test-matrix suite="unit" verbosity="normal" parallel="true":
    @echo "Test matrix: suite={{suite}} verbosity={{verbosity}} parallel={{parallel}}"

# Container matrix: [build|run|push|shell|scan] x [registry] x [tag]
container-matrix action="build" registry="ghcr.io/hyperpolymath" tag="latest":
    @echo "Container matrix: action={{action}} registry={{registry}} tag={{tag}}"

# CI matrix: [lint|test|build|security|all] x [quick|full]
ci-matrix stage="all" depth="quick":
    @echo "CI matrix: stage={{stage}} depth={{depth}}"

# Show all matrix combinations
combinations:
    @echo "=== Combinatoric Matrix Recipes ==="
    @echo ""
    @echo "Build Matrix: just build-matrix [debug|release] [target] [features]"
    @echo "Test Matrix:  just test-matrix [unit|integration|e2e|all] [verbosity] [parallel]"
    @echo "Container:    just container-matrix [build|run|push|shell|scan] [registry] [tag]"
    @echo "CI Matrix:    just ci-matrix [lint|test|build|security|all] [quick|full]"

# ═══════════════════════════════════════════════════════════════════════════════
# VERSION CONTROL
# ═══════════════════════════════════════════════════════════════════════════════

# Show git status
status:
    @git status --short

# Show recent commits
log count="20":
    @git log --oneline -{{count}}

# Generate CHANGELOG.md with git-cliff
changelog:
    @command -v git-cliff >/dev/null || { echo "git-cliff not found — install: cargo install git-cliff"; exit 1; }
    git cliff --config .machine_readable/configs/git-cliff/cliff.toml --output CHANGELOG.md
    @echo "Generated CHANGELOG.md"

# Preview changelog for unreleased commits (does not write)
changelog-preview:
    @command -v git-cliff >/dev/null || { echo "git-cliff not found — install: cargo install git-cliff"; exit 1; }
    git cliff --config .machine_readable/configs/git-cliff/cliff.toml --unreleased --strip header

# Tag a new release (usage: just release-tag 1.2.3)
release-tag version:
    #!/usr/bin/env bash
    TAG="v{{version}}"
    if git rev-parse "$TAG" >/dev/null 2>&1; then
        echo "Tag $TAG already exists"
        exit 1
    fi
    just changelog
    git add CHANGELOG.md
    git commit -m "chore(release): prepare $TAG"
    git tag -a "$TAG" -m "Release $TAG"
    echo "Created tag $TAG — push with: git push origin main --tags"

# ═══════════════════════════════════════════════════════════════════════════════
# UTILITIES
# ═══════════════════════════════════════════════════════════════════════════════

# Count lines of code
loc:
    @find . \( -name "*.rs" -o -name "*.ex" -o -name "*.exs" -o -name "*.res" -o -name "*.gleam" -o -name "*.zig" -o -name "*.idr" -o -name "*.hs" -o -name "*.ncl" -o -name "*.scm" -o -name "*.adb" -o -name "*.ads" \) -not -path './target/*' -not -path './_build/*' 2>/dev/null | xargs wc -l 2>/dev/null | tail -1 || echo "0"

# Show TODO comments
todos:
    @grep -rn "TODO\|FIXME\|HACK\|XXX" --include="*.rs" --include="*.ex" --include="*.res" --include="*.gleam" --include="*.zig" --include="*.idr" --include="*.hs" . 2>/dev/null || echo "No TODOs"

# Open in editor
edit:
    ${EDITOR:-code} .

# Run high-rigor security assault using panic-attacker
maint-assault:
    @./.machine_readable/scripts/maintenance/maint-assault.sh

# Run panic-attacker pre-commit scan (foundational floor-raise requirement)
assail:
    @command -v panic-attack >/dev/null 2>&1 && panic-attack assail . || echo "WARN: panic-attack not found — install from https://github.com/hyperpolymath/panic-attacker"


# Self-diagnostic — checks dependencies, permissions, paths
doctor:
    @echo "Running diagnostics for typed-wasm..."
    @echo "Checking required tools..."
    @command -v just >/dev/null 2>&1 && echo "  [OK] just" || echo "  [FAIL] just not found"
    @command -v git >/dev/null 2>&1 && echo "  [OK] git" || echo "  [FAIL] git not found"
    @echo "Checking for hardcoded paths..."
    @grep -rn '$HOME\|$ECLIPSE_DIR' --include='*.rs' --include='*.ex' --include='*.res' --include='*.gleam' --include='*.sh' . 2>/dev/null | head -5 || echo "  [OK] No hardcoded paths"
    @echo "Diagnostics complete."

# Auto-repair common issues
heal:
    @echo "Attempting auto-repair for typed-wasm..."
    @echo "Fixing permissions..."
    @find . -name "*.sh" -exec chmod +x {} \; 2>/dev/null || true
    @echo "Cleaning stale caches..."
    @rm -rf .cache/stale 2>/dev/null || true
    @echo "Repair complete."

# Guided tour of key features
tour:
    @echo "=== typed-wasm Tour ==="
    @echo ""
    @echo "1. Project structure:"
    @ls -la
    @echo ""
    @echo "2. Available commands: just --list"
    @echo ""
    @echo "3. Read README.adoc for full overview"
    @echo "4. Read EXPLAINME.adoc for architecture decisions"
    @echo "5. Run 'just doctor' to check your setup"
    @echo ""
    @echo "Tour complete! Try 'just --list' to see all available commands."

# Open feedback channel with diagnostic context
help-me:
    @echo "=== typed-wasm Help ==="
    @echo "Platform: $(uname -s) $(uname -m)"
    @echo "Shell: $SHELL"
    @echo ""
    @echo "To report an issue:"
    @echo "  https://github.com/hyperpolymath/typed-wasm/issues/new"
    @echo ""
    @echo "Include the output of 'just doctor' in your report."


# Print the current CRG grade (reads from READINESS.md '**Current Grade:** X' line)
crg-grade:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    echo "$$grade"

# Generate a shields.io badge markdown for the current CRG grade
# Looks for '**Current Grade:** X' in READINESS.md; falls back to X
crg-badge:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    case "$$grade" in \
      A) color="brightgreen" ;; B) color="green" ;; C) color="yellow" ;; \
      D) color="orange" ;; E) color="red" ;; F) color="critical" ;; \
      *) color="lightgrey" ;; esac; \
    echo "[![CRG $$grade](https://img.shields.io/badge/CRG-$$grade-$$color?style=flat-square)](https://github.com/hyperpolymath/standards/tree/main/component-readiness-grades)"
