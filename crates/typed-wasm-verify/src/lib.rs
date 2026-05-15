// SPDX-License-Identifier: PMPL-1.0-or-later
//
// typed-wasm post-codegen verifier.
//
// Statically verifies typed-wasm L7 (aliasing safety) and L10 (linearity)
// on emitted wasm modules. Reads the `affinescript.ownership` custom
// section, then runs per-path min/max use-range analysis on every
// function body in the module.
//
// Rust port of hyperpolymath/affinescript:
//   - lib/tw_verify.ml    (intra-function verifier, ~246 lines OCaml)
//   - lib/tw_interface.ml (cross-module boundary verifier, ~245 lines OCaml)
//
// The OCaml files are the spec of record until this crate reaches
// behavioural parity (tracked by C5 in the workspace task list).

use thiserror::Error;

pub mod cross;
pub mod section;
pub mod verify;
pub use cross::{extract_exports, verify_cross_module};
pub use section::{build_ownership_section_payload, parse_ownership_section_payload, OwnershipEntry};
pub use verify::{count_uses_range, verify_function};

/// Ownership kinds matching the OCaml `Codegen.ownership_kind` enum.
/// Wire encoding in the `affinescript.ownership` custom section: a single
/// u8 per kind, values 0/1/2/3 as below.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OwnershipKind {
    Unrestricted = 0,
    Linear = 1,
    SharedBorrow = 2,
    ExclBorrow = 3,
}

impl OwnershipKind {
    /// Decode a wire byte. Any value outside 0..=3 maps to `Unrestricted`
    /// — matches the OCaml `kind_of_byte` fallback.
    pub fn from_byte(b: u8) -> Self {
        match b {
            1 => OwnershipKind::Linear,
            2 => OwnershipKind::SharedBorrow,
            3 => OwnershipKind::ExclBorrow,
            _ => OwnershipKind::Unrestricted,
        }
    }

    /// Encode to the single-byte wire value.
    pub fn to_byte(self) -> u8 {
        self as u8
    }
}

/// An ownership violation found in a wasm function body.
/// Mirrors OCaml `Tw_verify.ownership_error`.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum OwnershipError {
    #[error("Level 10 violation: function {func_idx}, param {param_idx} — Linear (own) param dropped on all paths (must be consumed exactly once)")]
    LinearNotUsed { func_idx: u32, param_idx: u32 },

    #[error("Level 10 violation: function {func_idx}, param {param_idx} — Linear (own) param dropped on some paths (per-path min uses = 0; must be consumed on every path)")]
    LinearDroppedOnSomePath { func_idx: u32, param_idx: u32 },

    #[error("Level 10 violation: function {func_idx}, param {param_idx} — Linear (own) param loaded {count} times on some path (exactly 1 required; possible duplication)")]
    LinearUsedMultiple { func_idx: u32, param_idx: u32, count: u32 },

    #[error("Level 7 violation: function {func_idx}, param {param_idx} — ExclBorrow (mut) param aliased ({count} simultaneous references; at most 1 permitted)")]
    ExclBorrowAliased { func_idx: u32, param_idx: u32, count: u32 },
}

/// A cross-module ownership violation found in a caller's function body.
/// Mirrors OCaml `Tw_interface.cross_error`.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CrossError {
    #[error("Level 10 boundary violation: caller fn {caller_func_idx} calls import '{import_name}' {count} time(s) on some path (Linear param; must be called at most once)")]
    LinearImportCalledMultiple {
        caller_func_idx: u32,
        import_func_idx: u32,
        import_name: String,
        count: u32,
    },

    #[error("Level 10 boundary violation: caller fn {caller_func_idx} calls import '{import_name}' on some paths but not others (Linear param dropped on zero-call path)")]
    LinearImportDroppedOnSomePath {
        caller_func_idx: u32,
        import_func_idx: u32,
        import_name: String,
    },
}

/// Top-level verification failures (parse + verify).
#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("wasm parse error: {0}")]
    Parse(#[from] wasmparser::BinaryReaderError),

    #[error("ownership violations: {0:?}")]
    Ownership(Vec<OwnershipError>),

    #[error("cross-module boundary violations: {0:?}")]
    Cross(Vec<CrossError>),
}

/// Custom-section name carrying ownership annotations. Matches the OCaml
/// emitter (`Codegen.build_ownership_section`) and reader.
pub const OWNERSHIP_SECTION_NAME: &str = "affinescript.ownership";

// ----------------------------------------------------------------------
// Public entry points (stubbed in C1; implementations land in C2-C4).
// ----------------------------------------------------------------------

/// Verify the L7+L10 ownership constraints on a wasm module by reading its
/// embedded `affinescript.ownership` custom section. Returns `Ok(())` when
/// no violations are found; modules without the section verify trivially.
///
/// Rust port of OCaml `Tw_verify.verify_from_module`.
pub fn verify_from_module(wasm_bytes: &[u8]) -> Result<(), VerifyError> {
    verify::verify_from_module(wasm_bytes)
}

/// Ownership-annotated signature for one exported function.
/// Mirrors OCaml `Tw_interface.func_interface`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncInterface {
    pub name: String,
    pub func_idx: u32,
    pub param_kinds: Vec<OwnershipKind>,
    pub ret_kind: OwnershipKind,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ownership_kind_byte_roundtrip() {
        for (b, k) in [
            (0, OwnershipKind::Unrestricted),
            (1, OwnershipKind::Linear),
            (2, OwnershipKind::SharedBorrow),
            (3, OwnershipKind::ExclBorrow),
        ] {
            assert_eq!(OwnershipKind::from_byte(b), k);
        }
        assert_eq!(OwnershipKind::from_byte(99), OwnershipKind::Unrestricted);
    }
}
