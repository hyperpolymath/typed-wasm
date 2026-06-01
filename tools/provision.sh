#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tools/provision.sh — install the typed-wasm toolchain.
#
# Invoked by `just provision` (and, transitively, `just setup` / setup.sh).
# Idempotent: each tool is skipped if already on PATH.
#
# What it installs and why the install channel is what it is:
#   - Deno          JS runtime for the .mjs harnesses (estate npm→Deno, #133 /
#                   standards#253). Fetched from the GitHub *release assets*
#                   (github.com), because deno.land / dl.deno.land are denied by
#                   some network policies while github.com is reachable.
#   - wasmtime      capstone execution gate (#132), via crates.io (cargo install).
#   - AffineScript  the parser/codegen compiler. It is an OCaml program (NOT an
#                   npm package — `@hyperpolymath/affinescript` 404s on npmjs),
#                   built from hyperpolymath/affinescript with opam + dune. The
#                   pinned SHA matches .github/workflows/c5-regenerate.yml so the
#                   vendored C5.1 bytes stay reproducible.
#
# panic-attack classification:
#   io_operations: subprocess installers (curl/cargo/apt/opam/dune/git) and one
#   binary install per tool. Classification: setup-subprocess-install. No secrets
#   are read or written; all downloads are over https from pinned hosts/SHAs.

set -euo pipefail

# AffineScript revision — keep in lockstep with AFFINESCRIPT_SHA in
# .github/workflows/c5-regenerate.yml and the c5_real fixtures README.
AFFINESCRIPT_SHA="21edc159caee06a930cb7339b3e729ed5627b823"
OCAML_COMPILER="4.14.2"

SUDO=""
[ "$(id -u)" -ne 0 ] && command -v sudo >/dev/null 2>&1 && SUDO="sudo"
have() { command -v "$1" >/dev/null 2>&1; }
log()  { printf '  %s\n' "$1"; }

echo "== Provisioning typed-wasm toolchain =="

# ── Deno (JS runtime) ──────────────────────────────────────────────────────
if have deno; then
    log "deno present: $(deno --version | head -1)"
else
    log "installing Deno from GitHub release assets..."
    ver=$(curl -fsSLI -o /dev/null -w '%{url_effective}' \
        https://github.com/denoland/deno/releases/latest \
        | grep -oE 'v[0-9]+\.[0-9]+\.[0-9]+' | head -1)
    curl -fsSL -o /tmp/deno.zip \
        "https://github.com/denoland/deno/releases/download/${ver}/deno-x86_64-unknown-linux-gnu.zip"
    rm -rf /tmp/deno-bin
    if have unzip; then unzip -oq /tmp/deno.zip -d /tmp/deno-bin
    else python3 -c "import zipfile;zipfile.ZipFile('/tmp/deno.zip').extractall('/tmp/deno-bin')"; fi
    $SUDO install -m 0755 /tmp/deno-bin/deno /usr/local/bin/deno
    log "deno installed: $(deno --version | head -1)"
fi

# ── wasmtime (capstone execution gate, #132) ───────────────────────────────
if have wasmtime; then
    log "wasmtime present: $(wasmtime --version)"
elif have cargo; then
    log "installing wasmtime via cargo (crates.io)..."
    cargo install wasmtime-cli --locked
    log "wasmtime installed: $(wasmtime --version)"
else
    log "SKIP wasmtime — cargo not found (install Rust: https://rustup.rs)"
fi

# ── AffineScript (OCaml compiler, built from source) ───────────────────────
if have affinescript; then
    log "affinescript present"
else
    log "installing AffineScript (OCaml @ ${AFFINESCRIPT_SHA})..."
    if ! have opam; then
        $SUDO apt-get update -qq
        $SUDO apt-get install -y opam
    fi
    opam init --bare --no-setup --yes >/dev/null 2>&1 || true
    src="${AFFINESCRIPT_SRC:-/tmp/affinescript}"
    [ -d "$src/.git" ] || git clone https://github.com/hyperpolymath/affinescript "$src"
    git -C "$src" checkout -q "$AFFINESCRIPT_SHA"
    opam switch create "$src" "$OCAML_COMPILER" --yes >/dev/null 2>&1 \
        || opam switch set "$src" >/dev/null 2>&1 || true
    ( cd "$src" && opam install . --deps-only --yes && opam exec -- dune build )
    $SUDO install -m 0755 "$src/_build/default/bin/main.exe" /usr/local/bin/affinescript
    log "affinescript installed (main.exe @ ${AFFINESCRIPT_SHA})"
fi

echo "== Provision complete — run \`just deps\` to verify =="
