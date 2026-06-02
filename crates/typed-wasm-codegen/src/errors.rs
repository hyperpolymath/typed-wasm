// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Human-readable error messages — Phase 1 deliverable 6 (#126).
//!
//! The verifier reports rejections keyed by *function index* and *param
//! index* (e.g. "function 0, param 0 — Linear param loaded 2 times"). That
//! is precise but opaque to anyone who didn't write the verifier. This
//! module translates those rejections into actionable messages anchored to
//! the producer's **function names** (which the IR carries), explaining the
//! discipline that was violated and how to fix it.
//!
//! The remaining piece — anchoring to a `.twasm` **source line** ("…at line
//! N") — needs source spans from the front-end → IR seam (#127); the IR is
//! hand-built today and carries no spans. Until then, messages are
//! name-anchored, which is already a large step up from index-anchored.

use crate::Module;
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_from_module, AccessSiteError, CrossError,
    OwnershipError, VerifyError,
};

/// Render a global function index as the producer's source-level name
/// (`` `despawn_particle` ``), falling back to `function #N` for imports or
/// out-of-range indices.
fn func_name(module: &Module, func_idx: u32) -> String {
    let import_count = module.imports.len() as u32;
    if func_idx >= import_count {
        if let Some(f) = module.funcs.get((func_idx - import_count) as usize) {
            return format!("`{}`", f.name);
        }
    }
    format!("function #{func_idx}")
}

/// Translate one L7/L10/L13 ownership rejection.
pub fn humanize_ownership(module: &Module, e: &OwnershipError) -> String {
    match e {
        OwnershipError::LinearUsedMultiple {
            func_idx,
            param_idx,
            count,
        } => {
            let func = func_name(module, *func_idx);
            format!(
                "linearity (L10): in {func}, the `own` resource parameter #{param_idx} is used {count} \
                 times — an owned resource must be consumed exactly once (this duplicates / double-frees it)."
            )
        }
        OwnershipError::LinearNotUsed {
            func_idx,
            param_idx,
        } => {
            let func = func_name(module, *func_idx);
            format!(
                "linearity (L10): in {func}, the `own` resource parameter #{param_idx} is never consumed \
                 — an owned resource must be used exactly once (this leaks it)."
            )
        }
        OwnershipError::LinearDroppedOnSomePath {
            func_idx,
            param_idx,
        } => {
            let func = func_name(module, *func_idx);
            format!(
                "linearity (L10): in {func}, the `own` resource parameter #{param_idx} is consumed on some \
                 paths but dropped on others — consume it on every path."
            )
        }
        OwnershipError::ExclBorrowAliased {
            func_idx,
            param_idx,
            count,
        } => {
            let func = func_name(module, *func_idx);
            format!(
                "aliasing (L7): in {func}, the `&mut` (exclusive) parameter #{param_idx} is referenced \
                 {count} times at once — at most one exclusive reference may be live."
            )
        }
        OwnershipError::ModuleNotIsolated { reason } => {
            format!("module isolation (L13): {reason}")
        }
    }
}

/// Translate one L10 cross-module boundary rejection.
pub fn humanize_cross(module: &Module, e: &CrossError) -> String {
    match e {
        CrossError::LinearImportCalledMultiple {
            caller_func_idx,
            import_name,
            count,
            ..
        } => {
            let func = func_name(module, *caller_func_idx);
            format!(
                "linearity (L10, cross-module): {func} calls the linear import `{import_name}` {count} \
                 times on some path — a linear import must be called at most once (this duplicates the resource)."
            )
        }
        CrossError::LinearImportDroppedOnSomePath {
            caller_func_idx,
            import_name,
            ..
        } => {
            let func = func_name(module, *caller_func_idx);
            format!(
                "linearity (L10, cross-module): {func} calls the linear import `{import_name}` on some paths \
                 but not others — transfer the resource on every path."
            )
        }
    }
}

/// Translate one L2 access-site rejection.
pub fn humanize_access_site(module: &Module, e: &AccessSiteError) -> String {
    match e {
        AccessSiteError::MissingDependentRegions =>
            "region binding (L2): the module emitted a `typedwasm.access-sites` section without the \
             companion `typedwasm.regions` schema — typed accesses have nothing to resolve against."
                .to_string(),
        AccessSiteError::FuncIdxOutOfRange {
            entry_idx,
            func_idx,
            function_count,
        } => {
            let func = func_name(module, *func_idx);
            format!(
                "region binding (L2): access-site #{entry_idx} names {func} (index {func_idx}), but the \
                 module only has {function_count} functions."
            )
        }
        AccessSiteError::RegionIdOutOfRange {
            entry_idx,
            region_id,
            region_count,
        } => format!(
            "region binding (L2): access-site #{entry_idx} references region {region_id}, but only \
             {region_count} regions are declared."
        ),
        AccessSiteError::FieldIdOutOfRange {
            entry_idx,
            region_id,
            field_id,
            field_count,
        } => format!(
            "region binding (L2): access-site #{entry_idx} references field {field_id} of region \
             {region_id}, which only has {field_count} fields."
        ),
    }
}

/// Translate any top-level [`VerifyError`] into one message per violation.
pub fn humanize(module: &Module, err: &VerifyError) -> Vec<String> {
    match err {
        VerifyError::Ownership(es) => es.iter().map(|e| humanize_ownership(module, e)).collect(),
        VerifyError::Cross(es) => es.iter().map(|e| humanize_cross(module, e)).collect(),
        VerifyError::Parse(e) => {
            vec![format!("the emitted module is not valid wasm: {e}")]
        }
    }
}

/// Emit `module`, re-verify the bytes, and return human-readable
/// diagnostics for every violation found.
///
/// This is the producer's self-check: it turns the Phase-2 gate's
/// "on a violation, receive an error message they can act on" into reality
/// by running the verifier on its own output and translating the result.
/// `Ok(())` means the emitted module passed L2 + L7/L10.
pub fn self_verify(module: &Module) -> Result<(), Vec<String>> {
    let bytes = crate::emit(module);
    let mut msgs = Vec::new();

    if let Err(e) = verify_from_module(&bytes) {
        msgs.extend(humanize(module, &e));
    }
    match verify_access_sites_from_module(&bytes) {
        Ok(violations) => msgs.extend(violations.iter().map(|e| humanize_access_site(module, e))),
        Err(e) => msgs.extend(humanize(module, &e)),
    }

    if msgs.is_empty() {
        Ok(())
    } else {
        Err(msgs)
    }
}
