// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! Load-time enforcement gate — the Phase 3 slice (runtime-side
//! enforcement, issue #51).
//!
//! Build-time verification (`tw build` self-verify, `tw link`) trusts
//! whoever ran the build. This crate moves the trust boundary to the
//! LOADER: a [`VerifiedModule`] is a witness type whose only
//! constructors are [`gate_module`] / [`gate_link_graph`], which run
//! the full typed-wasm verifier stack over the raw bytes — structural
//! validation, L7/L10 ownership/linearity, L2 carrier bounds + access
//! typing, L13 region-import consistency, and (for graphs) cross-module
//! `SchemaSub` certification. Instantiation adapters accept only
//! `&VerifiedModule`, so an unverified or violating module cannot reach
//! a runtime through this crate's API at all.
//!
//! The gate is runtime-agnostic: it consumes bytes and returns a
//! witness + [`GateReport`]. The `wasmi-runtime` feature provides an
//! in-process adapter (pure Rust, CI-testable); a wasmtime adapter is
//! the documented follow-up and needs nothing from the gate beyond
//! what `wasmi::instantiate_verified` already uses.

use thiserror::Error;
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_access_typing_from_module, verify_from_module,
    verify_link_graph, verify_region_imports_from_module, AccessSiteError, CompatCertificate,
    RegionImportsError, VerifyError,
};

/// Why the gate refused a module (first failing layer reported).
#[derive(Debug, Error)]
pub enum GateError {
    /// Not decodable as wasm at all, or an L7/L10/L13-negative
    /// ownership violation (see the inner error).
    #[error("ownership/linearity verification failed: {0}")]
    Ownership(#[from] VerifyError),

    /// L2 carrier bounds violations (`typedwasm.regions` /
    /// `typedwasm.access-sites` internal consistency).
    #[error("L2 access-site bounds violations: {0:?}")]
    AccessSites(Vec<AccessSiteError>),

    /// L2 access-typing violations: a pinned instruction is not the
    /// right memory op at the right offset for its claimed field.
    #[error("L2 access-typing violations: {0:?}")]
    AccessTyping(Vec<String>),

    /// L13 region-import violations — module-local inconsistency, or
    /// (in a link graph) unresolved producers / schema disagreement.
    #[error("L13 region-import violations: {0:?}")]
    RegionImports(Vec<RegionImportsError>),
}

/// What the gate established about a module it passed.
#[derive(Debug, Clone, Default)]
pub struct GateReport {
    /// Pinned access sites whose instruction-level typing was checked.
    pub typed_sites_checked: u32,
    /// Declared-only (unpinned) access sites — counted, not checked.
    pub declared_only_sites: u32,
    /// Cross-module certificates this module participates in as the
    /// consumer (link-graph gate only; empty for single-module gates).
    pub certificates: Vec<CompatCertificate>,
}

/// Witness that `bytes` passed the gate. The field is private and the
/// only constructors run the verifier stack — possession of a
/// `VerifiedModule` IS the proof of verification.
#[derive(Debug, Clone)]
pub struct VerifiedModule {
    bytes: Vec<u8>,
    report: GateReport,
}

impl VerifiedModule {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn report(&self) -> &GateReport {
        &self.report
    }
}

/// Run the single-module verifier stack; a `VerifiedModule` comes back
/// only if every layer passes.
pub fn gate_module(bytes: &[u8]) -> Result<VerifiedModule, GateError> {
    // L7 / L10 / L13-negative (also rejects undecodable bytes).
    verify_from_module(bytes)?;

    // L2 carrier bounds.
    let bounds = verify_access_sites_from_module(bytes)?;
    if !bounds.is_empty() {
        return Err(GateError::AccessSites(bounds));
    }

    // L2 access typing on pinned sites.
    let typing = verify_access_typing_from_module(bytes)?;
    if !typing.errors.is_empty() {
        return Err(GateError::AccessTyping(
            typing.errors.iter().map(|e| e.to_string()).collect(),
        ));
    }

    // L13 module-local import-table consistency.
    let import_errs = verify_region_imports_from_module(bytes)?;
    if !import_errs.is_empty() {
        return Err(GateError::RegionImports(import_errs));
    }

    Ok(VerifiedModule {
        bytes: bytes.to_vec(),
        report: GateReport {
            typed_sites_checked: typing.type_verified,
            declared_only_sites: typing.declared_only,
            certificates: Vec::new(),
        },
    })
}

/// Gate a whole link graph: every module passes the single-module gate
/// AND cross-module schema agreement holds (`verify_link_graph`,
/// ADR-0007). Returns the witnesses in input order, each consumer's
/// certificates attached to its report.
pub fn gate_link_graph(
    named: &[(&str, &[u8])],
) -> Result<Vec<(String, VerifiedModule)>, GateError> {
    let mut gated: Vec<(String, VerifiedModule)> = Vec::new();
    for (name, bytes) in named {
        gated.push((name.to_string(), gate_module(bytes)?));
    }
    let report = verify_link_graph(named)?;
    if !report.errors.is_empty() {
        return Err(GateError::RegionImports(report.errors));
    }
    for cert in report.certificates {
        if let Some((_, module)) = gated.iter_mut().find(|(n, _)| *n == cert.consumer) {
            module.report.certificates.push(cert);
        }
    }
    Ok(gated)
}

/// In-process instantiation adapter backed by wasmi. Accepts only the
/// gate's witness type — this is the enforcement point.
#[cfg(feature = "wasmi-runtime")]
pub mod wasmi_runtime {
    use super::VerifiedModule;

    /// Load + instantiate a verified module in a wasmi store. All
    /// wasmi-level errors pass through untouched; what this adapter
    /// adds is the TYPE-LEVEL guarantee that `module` went through the
    /// gate.
    pub fn instantiate_verified(
        engine: &wasmi::Engine,
        store: &mut wasmi::Store<()>,
        linker: &wasmi::Linker<()>,
        module: &VerifiedModule,
    ) -> Result<wasmi::Instance, wasmi::Error> {
        let compiled = wasmi::Module::new(engine, module.bytes())?;
        linker.instantiate_and_start(store, &compiled)
    }
}
