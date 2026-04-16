# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# K9 Validator: Typed Wasm Guard
# Ensures the Typed Wasm project keeps its memory-safety contracts and parser invariants intact.

let typed_wasm_guard = {
  name = "typed-wasm-guard",
  version = "1.0.0",
  description = "Validates the core invariants for Typed Wasm (multi-module safety, lifetime tracking, parser integrity, and no template placeholders).",

  checks = {
    multi_module = {
      description = "The Idris2 MultiModule proof exists in the ABI folder.",
      severity = "error",
      check_type = "file-exists",
      file = "src/abi/TypedWasm/ABI/MultiModule.idr",
    },

    lifetime_proof = {
      description = "The Lifetime proof provides region-lifetime semantics.",
      severity = "error",
      check_type = "file-exists",
      file = "src/abi/TypedWasm/ABI/Lifetime.idr",
    },

    levels_semantics = {
      description = "The Levels semantics file is present for the 10-level lattice.",
      severity = "warning",
      check_type = "file-exists",
      file = "src/abi/TypedWasm/ABI/Levels.idr",
    },

    parser_integrity = {
      description = "The ReScript parser definition is included.",
      severity = "error",
      check_type = "file-exists",
      file = "src/parser/Parser.res",
    },

    no_template_placeholders = {
      description = "No TYPED_WASM/  tokens remain in the source base.",
      severity = "error",
      check_type = "file-pattern-guard",
      scope = ".",
      reject_patterns = ["TYPED_WASM", "", "rsr-template-repo"],
    },

    placeholder_fuzz_absent = {
      description = "The placeholder fuzz file must not exist—it gives false security.",
      severity = "warning",
      check_type = "file-not-exists",
      file = "tests/fuzz/placeholder.txt",
    },
  },
}
in typed_wasm_guard
