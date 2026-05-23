// SPDX-License-Identifier: MPL-2.0
//
// Cross-module boundary verifier.
//
// Rust port of `Tw_interface.extract_exports` and
// `Tw_interface.verify_cross_module` from
// hyperpolymath/affinescript/lib/tw_interface.ml.
//
// The intra-function verifier (the `verify` module) checks each function
// body against its own declared param kinds. This module closes the
// full-stack loop by checking that **caller modules** invoke
// Linear-annotated **imports** with consistent per-path call counts:
//
//   - `max_calls > 1` on any path → `LinearImportCalledMultiple` (a
//     Linear argument may be duplicated by the second call site)
//   - `min_calls = 0, max_calls ≥ 1` → `LinearImportDroppedOnSomePath`
//     (the argument is dropped without transfer on the zero-call path)
//
// The same `(min, max)` frame-stack analysis from the intra-function
// pass is reused: just swap the `LocalGetOf` counter for a `CallOf` one.

use std::collections::HashMap;

use wasmparser::{FunctionBody, Parser, Payload};

use crate::section::parse_ownership_section_payload;
use crate::verify::{count_op_range, CallOf};
use crate::{CrossError, FuncInterface, OwnershipKind, VerifyError, OWNERSHIP_SECTION_NAME};

// ----------------------------------------------------------------------
// Interface extraction (callee side)
// ----------------------------------------------------------------------

/// Extract the ownership-annotated export interface of a wasm module.
/// One entry per exported function; non-function exports (tables,
/// memories, globals) are filtered out. Functions without an entry in
/// the ownership section are treated as fully `Unrestricted`.
///
/// Rust port of OCaml `Tw_interface.extract_exports`.
pub fn extract_exports(wasm_bytes: &[u8]) -> Result<Vec<FuncInterface>, VerifyError> {
    let mut ownership_payload: Option<Vec<u8>> = None;
    let mut func_exports: Vec<(String, u32)> = Vec::new();

    let parser = Parser::new(0);
    for payload in parser.parse_all(wasm_bytes) {
        match payload? {
            Payload::CustomSection(reader) if reader.name() == OWNERSHIP_SECTION_NAME => {
                ownership_payload = Some(reader.data().to_vec());
            }
            Payload::ExportSection(reader) => {
                for export in reader {
                    let export = export?;
                    if let wasmparser::ExternalKind::Func = export.kind {
                        func_exports.push((export.name.to_string(), export.index));
                    }
                }
            }
            _ => {}
        }
    }

    // Build a func_idx → (param_kinds, ret_kind) lookup from the
    // ownership section if it exists. Mirrors OCaml
    // `Tw_interface.ownership_index_of_module`.
    let ownership_by_idx: HashMap<u32, (Vec<OwnershipKind>, OwnershipKind)> =
        match ownership_payload {
            Some(payload) => parse_ownership_section_payload(&payload)
                .into_iter()
                .map(|e| (e.func_idx, (e.param_kinds, e.ret_kind)))
                .collect(),
            None => HashMap::new(),
        };

    Ok(func_exports
        .into_iter()
        .map(|(name, func_idx)| {
            let (param_kinds, ret_kind) = ownership_by_idx
                .get(&func_idx)
                .cloned()
                .unwrap_or_else(|| (Vec::new(), OwnershipKind::Unrestricted));
            FuncInterface {
                name,
                func_idx,
                param_kinds,
                ret_kind,
            }
        })
        .collect())
}

// ----------------------------------------------------------------------
// Cross-module verification (caller side)
// ----------------------------------------------------------------------

/// Verify that a caller module's local function bodies respect the
/// ownership annotations of a callee's exported interface.
///
/// For each import in `caller_bytes` that matches a Linear-param export
/// in `callee_iface` (by export name), every local function in the
/// caller is inspected:
///
///   - `max_calls > 1`  → `LinearImportCalledMultiple`
///   - `min_calls == 0` with `max_calls ≥ 1`  → `LinearImportDroppedOnSomePath`
///   - `max_calls == 0` (function never calls the import) → ignored;
///     functions are not required to invoke every import
///
/// Both drop and dup can fire for the same caller/import pair if
/// `min=0, max>1`.
///
/// Rust port of OCaml `Tw_interface.verify_cross_module`.
pub fn verify_cross_module(
    callee_iface: &[FuncInterface],
    caller_bytes: &[u8],
) -> Result<(), VerifyError> {
    // Index callee exports by name for O(1) lookup against caller imports.
    let iface_by_name: HashMap<&str, &FuncInterface> = callee_iface
        .iter()
        .map(|fi| (fi.name.as_str(), fi))
        .collect();

    // Walk caller: capture (import_slot, import_name) for every
    // function-typed import whose name matches a callee export with at
    // least one Linear param. Capture every local function body too.
    let mut linear_imports: Vec<(u32, String)> = Vec::new();
    let mut bodies: Vec<FunctionBody<'_>> = Vec::new();
    let mut next_import_slot: u32 = 0;

    let parser = Parser::new(0);
    for payload in parser.parse_all(caller_bytes) {
        match payload? {
            Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    let import = import?;
                    // Only function imports occupy slots in the function
                    // index space — table/memory/global imports don't.
                    if matches!(import.ty, wasmparser::TypeRef::Func(_)) {
                        let slot = next_import_slot;
                        next_import_slot += 1;
                        if let Some(fi) = iface_by_name.get(import.name) {
                            if fi.param_kinds.contains(&OwnershipKind::Linear) {
                                linear_imports.push((slot, import.name.to_string()));
                            }
                        }
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                bodies.push(body);
            }
            _ => {}
        }
    }

    // If no Linear-param imports are wired in, there's nothing to check.
    if linear_imports.is_empty() {
        return Ok(());
    }

    let import_count = next_import_slot;
    let mut errors: Vec<CrossError> = Vec::new();

    for (import_slot, import_name) in &linear_imports {
        for (local_idx, body) in bodies.iter().enumerate() {
            let caller_func_idx = (local_idx as u32) + import_count;
            let (min_calls, max_calls) = count_op_range(body.clone(), &CallOf(*import_slot))?;

            if max_calls == 0 {
                // Function never calls this import: not a violation.
                // Functions are not obligated to use every import.
                continue;
            }
            if min_calls == 0 {
                errors.push(CrossError::LinearImportDroppedOnSomePath {
                    caller_func_idx,
                    import_func_idx: *import_slot,
                    import_name: import_name.clone(),
                });
            }
            if max_calls > 1 {
                errors.push(CrossError::LinearImportCalledMultiple {
                    caller_func_idx,
                    import_func_idx: *import_slot,
                    import_name: import_name.clone(),
                    count: max_calls,
                });
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(VerifyError::Cross(errors))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::section::build_ownership_section_payload;
    use crate::OwnershipEntry;
    use wasm_encoder::{
        BlockType, CodeSection, CustomSection, EntityType, ExportKind, ExportSection, Function,
        FunctionSection, ImportSection, Instruction, Module, TypeSection, ValType,
    };

    /// Build a callee module with one exported function `name` whose
    /// param kinds are recorded in an `affinescript.ownership` section.
    /// The function body is trivial (just returns).
    fn callee_module(export_name: &str, param_kinds: Vec<OwnershipKind>) -> Vec<u8> {
        let n_params = param_kinds.len() as u32;
        let mut module = Module::new();

        let mut types = TypeSection::new();
        types.ty().function((0..n_params).map(|_| ValType::I32), []);
        module.section(&types);

        let mut funcs = FunctionSection::new();
        funcs.function(0);
        module.section(&funcs);

        let mut exports = ExportSection::new();
        exports.export(export_name, ExportKind::Func, 0);
        module.section(&exports);

        let mut code = CodeSection::new();
        let f = Function::new([]);
        // Empty body — wasm-encoder's Function does NOT auto-append End,
        // but a function body must end with End to be valid. We compose
        // bodies manually elsewhere; here we want an empty body that
        // still validates, so we add End explicitly.
        let mut f = f;
        f.instruction(&Instruction::End);
        code.function(&f);
        module.section(&code);

        let payload = build_ownership_section_payload(&[OwnershipEntry {
            func_idx: 0,
            param_kinds,
            ret_kind: OwnershipKind::Unrestricted,
        }]);
        let custom = CustomSection {
            name: OWNERSHIP_SECTION_NAME.into(),
            data: payload.as_slice().into(),
        };
        module.section(&custom);

        module.finish()
    }

    /// Build a caller module with one import (1-i32-param, no return)
    /// from `("host", import_field)` and one local function per body in
    /// `bodies`. Each local function takes 1 i32 param.
    fn caller_module(import_field: &str, bodies: Vec<Vec<Instruction<'_>>>) -> Vec<u8> {
        let mut module = Module::new();

        // Two function types: type 0 = (i32) -> (), shared by the
        // import and every local function.
        let mut types = TypeSection::new();
        types.ty().function([ValType::I32], []);
        module.section(&types);

        let mut imports = ImportSection::new();
        imports.import("host", import_field, EntityType::Function(0));
        module.section(&imports);

        let mut funcs = FunctionSection::new();
        for _ in &bodies {
            funcs.function(0);
        }
        module.section(&funcs);

        let mut code = CodeSection::new();
        for body in bodies {
            let mut f = Function::new([]);
            for instr in &body {
                f.instruction(instr);
            }
            f.instruction(&Instruction::End);
            code.function(&f);
        }
        module.section(&code);

        module.finish()
    }

    // ------------------------------------------------------------------
    // extract_exports
    // ------------------------------------------------------------------

    #[test]
    fn extract_exports_finds_linear_param() {
        let bytes = callee_module("consume_string", vec![OwnershipKind::Linear]);
        let ifaces = extract_exports(&bytes).unwrap();
        assert_eq!(
            ifaces,
            vec![FuncInterface {
                name: "consume_string".to_string(),
                func_idx: 0,
                param_kinds: vec![OwnershipKind::Linear],
                ret_kind: OwnershipKind::Unrestricted,
            }]
        );
    }

    #[test]
    fn extract_exports_module_without_ownership_section() {
        // Same shape as callee_module but no custom section. Such a
        // module's exports are reported as `Unrestricted` with no
        // param kinds, matching OCaml's fallback.
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([ValType::I32], []);
        module.section(&types);
        let mut funcs = FunctionSection::new();
        funcs.function(0);
        module.section(&funcs);
        let mut exports = ExportSection::new();
        exports.export("plain", ExportKind::Func, 0);
        module.section(&exports);
        let mut code = CodeSection::new();
        let mut f = Function::new([]);
        f.instruction(&Instruction::End);
        code.function(&f);
        module.section(&code);
        let bytes = module.finish();

        let ifaces = extract_exports(&bytes).unwrap();
        assert_eq!(
            ifaces,
            vec![FuncInterface {
                name: "plain".to_string(),
                func_idx: 0,
                param_kinds: vec![],
                ret_kind: OwnershipKind::Unrestricted,
            }]
        );
    }

    #[test]
    fn extract_exports_empty_module() {
        let bytes = Module::new().finish();
        assert_eq!(extract_exports(&bytes).unwrap(), vec![]);
    }

    // ------------------------------------------------------------------
    // verify_cross_module
    // ------------------------------------------------------------------

    #[test]
    fn linear_import_called_exactly_once_is_clean() {
        let callee = callee_module("consume", vec![OwnershipKind::Linear]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "consume",
            vec![vec![Instruction::LocalGet(0), Instruction::Call(0)]],
        );
        assert!(verify_cross_module(&iface, &caller).is_ok());
    }

    #[test]
    fn linear_import_called_twice_errors() {
        let callee = callee_module("consume", vec![OwnershipKind::Linear]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "consume",
            vec![vec![
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::LocalGet(0),
                Instruction::Call(0),
            ]],
        );
        match verify_cross_module(&iface, &caller) {
            Err(VerifyError::Cross(errs)) => {
                assert!(matches!(
                    errs.as_slice(),
                    [CrossError::LinearImportCalledMultiple {
                        caller_func_idx: 1, // import_count(1) + local_idx(0)
                        import_func_idx: 0,
                        count: 2,
                        ..
                    }]
                ));
                if let CrossError::LinearImportCalledMultiple { import_name, .. } = &errs[0] {
                    assert_eq!(import_name, "consume");
                } else {
                    unreachable!();
                }
            }
            other => panic!("expected LinearImportCalledMultiple, got {:?}", other),
        }
    }

    #[test]
    fn linear_import_dropped_on_some_path_errors() {
        // if (local 0) { call 0 } — no else, so import called on
        // exactly one of two paths.
        let callee = callee_module("consume", vec![OwnershipKind::Linear]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "consume",
            vec![vec![
                Instruction::LocalGet(0),
                Instruction::If(BlockType::Empty),
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::End,
            ]],
        );
        match verify_cross_module(&iface, &caller) {
            Err(VerifyError::Cross(errs)) => {
                assert!(matches!(
                    errs.as_slice(),
                    [CrossError::LinearImportDroppedOnSomePath {
                        caller_func_idx: 1,
                        import_func_idx: 0,
                        ..
                    }]
                ));
            }
            other => panic!("expected LinearImportDroppedOnSomePath, got {:?}", other),
        }
    }

    #[test]
    fn linear_import_never_called_by_some_caller_fns_is_clean() {
        // Three caller fns: only the first calls the import. Functions
        // that never call the import shouldn't be flagged — there's no
        // obligation for every fn to invoke every import.
        let callee = callee_module("consume", vec![OwnershipKind::Linear]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "consume",
            vec![
                vec![Instruction::LocalGet(0), Instruction::Call(0)],
                vec![Instruction::LocalGet(0), Instruction::Drop],
                vec![Instruction::LocalGet(0), Instruction::Drop],
            ],
        );
        assert!(verify_cross_module(&iface, &caller).is_ok());
    }

    #[test]
    fn non_linear_import_unconstrained() {
        // Callee export has only Unrestricted params → caller can call
        // it any number of times with no violation.
        let callee = callee_module("noop", vec![OwnershipKind::Unrestricted]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "noop",
            vec![vec![
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::LocalGet(0),
                Instruction::Call(0),
            ]],
        );
        assert!(verify_cross_module(&iface, &caller).is_ok());
    }

    #[test]
    fn excl_borrow_import_unconstrained_at_boundary() {
        // ExclBorrow is intra-function only. Cross-module verification
        // only enforces Linear; ExclBorrow imports are not checked here
        // (the affinescript design: ExclBorrow can't escape its
        // function in the source language, so the boundary is never
        // crossed by one).
        let callee = callee_module("borrow_mut", vec![OwnershipKind::ExclBorrow]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "borrow_mut",
            vec![vec![
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::LocalGet(0),
                Instruction::Call(0),
            ]],
        );
        assert!(verify_cross_module(&iface, &caller).is_ok());
    }

    #[test]
    fn linear_import_unmatched_export_is_ignored() {
        // Caller imports "missing" but the callee doesn't export it.
        // No violation can be checked → trivially Ok.
        let callee = callee_module("consume", vec![OwnershipKind::Linear]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "missing", // different name from callee's export
            vec![vec![
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::LocalGet(0),
                Instruction::Call(0),
            ]],
        );
        assert!(verify_cross_module(&iface, &caller).is_ok());
    }

    #[test]
    fn linear_import_drop_and_dup_both_fire() {
        // if (lg0) { call 0; call 0 } — min_calls=0 (else path),
        // max_calls=2 (then path). Both error variants fire for the
        // same (caller_fn, import) pair.
        let callee = callee_module("consume", vec![OwnershipKind::Linear]);
        let iface = extract_exports(&callee).unwrap();
        let caller = caller_module(
            "consume",
            vec![vec![
                Instruction::LocalGet(0),
                Instruction::If(BlockType::Empty),
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::LocalGet(0),
                Instruction::Call(0),
                Instruction::End,
            ]],
        );
        match verify_cross_module(&iface, &caller) {
            Err(VerifyError::Cross(errs)) => {
                assert_eq!(errs.len(), 2);
                assert!(errs
                    .iter()
                    .any(|e| matches!(e, CrossError::LinearImportDroppedOnSomePath { .. })));
                assert!(errs
                    .iter()
                    .any(|e| matches!(e, CrossError::LinearImportCalledMultiple { count: 2, .. })));
            }
            other => panic!("expected 2 errors, got {:?}", other),
        }
    }
}
