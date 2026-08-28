# SPDX-License-Identifier: MPL-2.0
# shellcheck shell=bash
# Layering-contract gate config for typed-wasm. Consumed by tools/check-contract.sh.
# See CONTRACT.adoc for the human-readable rules.

# This repo's role in the stack: theory | kernel | target | profile | producer
CONTRACT_ROLE="target"

# I1 — dependency direction. typed-wasm is a shared *target*; none of its
# producers/consumers (or upstream theory/kernel) may appear as a dependency here.
CONTRACT_FORBIDDEN_DEPS="affinescript ephapax anytype systemet"
CONTRACT_MANIFESTS="Cargo.toml deno.json crates/typed-wasm-verify/Cargo.toml crates/typed-wasm-codegen/Cargo.toml"

# I3 — the typedwasm.* wire ABI (multi-producer). Anchored byte-spec regions;
# a change fails the gate unless abi_version is bumped + an ADR referenced + --reseal.
CONTRACT_ABI_VERSION="1"
CONTRACT_ABI_ANCHORS="crates/typed-wasm-verify/src/section.rs::ownership crates/typed-wasm-verify/src/section.rs::regions"

# I4 — role purity (advisory). A target must not embed producer-specific lowering.
# (Left empty: the target's purity is governed mainly by I1; greps here would
# false-positive on the cross-impl parity comments.)
CONTRACT_ROLE_DENY=""
CONTRACT_SRC_DIRS="crates"
