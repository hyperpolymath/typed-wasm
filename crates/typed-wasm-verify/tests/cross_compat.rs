// SPDX-License-Identifier: MPL-2.0
//
// Cross-compatibility regression suite for `typed-wasm-verify`.
//
// Scope
// =====
//
// These tests build larger, multi-function wasm modules that model what
// the OCaml emitter in `hyperpolymath/affinescript:lib/codegen.ml` would
// produce for representative AffineScript source programs. They are
// **integration tests**, separate from the per-feature unit tests in
// `src/{verify,cross,section}.rs`, and they exist to:
//
//   1. **Catch verifier drift** — if a future change to the Rust
//      verifier subtly alters its verdict on a realistic module, this
//      suite fails before the change reaches `main`.
//   2. **Document semantic parity with the OCaml reference** — each
//      fixture's doc comment includes the conceptual AffineScript
//      source it represents AND the verdict the OCaml verifier
//      (`Tw_verify` + `Tw_interface`) should produce on the same wasm.
//      The Rust verdict asserted here must match the OCaml one;
//      divergence either side is a parity bug.
//   3. **Anchor the wire format** — the fixtures emit the exact same
//      `typedwasm.ownership` custom-section bytes that
//      `Codegen.build_ownership_section` would emit, exercising the C2
//      codec end-to-end.
//
// What this suite is NOT (yet)
// ----------------------------
//
// We do not currently invoke `affinescript build` to produce real
// OCaml-emitted .wasm fixtures and compare verdicts byte-for-byte.
// That requires a built `affinescript` binary in PATH (dune build of
// hyperpolymath/affinescript). Wiring that up is a separate follow-up
// (call it C5.1) — when it lands, these synthetic fixtures stay (they
// cover edge cases that may not appear in any AS source program) and
// the OCaml-emitted ones get added alongside.
//
// Until then, the **expected OCaml verdict** lines in each fixture
// header are computed by hand-tracing `tw_verify.ml` / `tw_interface.ml`
// over the wasm structure. If you change those OCaml files'
// semantics, update both this suite and the corresponding `src/*.rs`
// match.

use typed_wasm_verify::{
    build_ownership_section_payload, extract_exports, verify_cross_module, verify_from_module,
    CrossError, OwnershipEntry, OwnershipError, OwnershipKind, VerifyError, OWNERSHIP_SECTION_NAME,
};
use wasm_encoder::{
    BlockType, CodeSection, CustomSection, EntityType, ExportKind, ExportSection, Function,
    FunctionSection, ImportSection, Instruction, Module, TypeSection, ValType,
};

// ----------------------------------------------------------------------
// Fixture builders
// ----------------------------------------------------------------------

/// Builder for an `affinescript`-shaped module with multiple functions
/// and an `typedwasm.ownership` custom section.
struct ModuleBuilder {
    types: TypeSection,
    funcs: FunctionSection,
    code: CodeSection,
    exports: ExportSection,
    imports: ImportSection,
    ownership: Vec<OwnershipEntry>,
    type_idx: u32,
    import_count: u32,
    local_func_count: u32,
}

impl ModuleBuilder {
    fn new() -> Self {
        Self {
            types: TypeSection::new(),
            funcs: FunctionSection::new(),
            code: CodeSection::new(),
            exports: ExportSection::new(),
            imports: ImportSection::new(),
            ownership: Vec::new(),
            type_idx: 0,
            import_count: 0,
            local_func_count: 0,
        }
    }

    /// Register a new function type. Returns the type index.
    fn add_type(&mut self, params: Vec<ValType>, results: Vec<ValType>) -> u32 {
        self.types.ty().function(params, results);
        let idx = self.type_idx;
        self.type_idx += 1;
        idx
    }

    /// Add a function import. Returns the import's global function index.
    fn add_import(&mut self, module: &str, field: &str, type_idx: u32) -> u32 {
        self.imports
            .import(module, field, EntityType::Function(type_idx));
        let slot = self.import_count;
        self.import_count += 1;
        slot
    }

    /// Add a local function with the given body instructions (trailing
    /// `End` appended automatically) and ownership annotation. Returns
    /// the global function index.
    fn add_function(
        &mut self,
        type_idx: u32,
        body: &[Instruction<'_>],
        param_kinds: Vec<OwnershipKind>,
    ) -> u32 {
        self.funcs.function(type_idx);
        let mut f = Function::new([]);
        for instr in body {
            f.instruction(instr);
        }
        f.instruction(&Instruction::End);
        self.code.function(&f);

        let global_idx = self.import_count + self.local_func_count;
        self.local_func_count += 1;

        if !param_kinds.is_empty() {
            self.ownership.push(OwnershipEntry {
                func_idx: global_idx,
                param_kinds,
                ret_kind: OwnershipKind::Unrestricted,
            });
        }
        global_idx
    }

    /// Export an already-added function.
    fn export_function(&mut self, name: &str, func_idx: u32) {
        self.exports.export(name, ExportKind::Func, func_idx);
    }

    fn finish(self) -> Vec<u8> {
        let mut module = Module::new();
        module.section(&self.types);
        if self.import_count > 0 {
            module.section(&self.imports);
        }
        module.section(&self.funcs);
        module.section(&self.exports);
        module.section(&self.code);
        if !self.ownership.is_empty() {
            let payload = build_ownership_section_payload(&self.ownership);
            let custom = CustomSection {
                name: OWNERSHIP_SECTION_NAME.into(),
                data: payload.as_slice().into(),
            };
            module.section(&custom);
        }
        module.finish()
    }
}

// ----------------------------------------------------------------------
// Fixture 1 — Clean Linear consumer
// ----------------------------------------------------------------------
//
// Conceptual AffineScript:
//
//     fn consume(s: own String): unit = drop s
//
// Emitted wasm has one local function:
//   - Param 0 is Linear (ownership byte = 1)
//   - Body loads param 0 once and discards it
//
// Expected OCaml verdict (tw_verify.verify_function):
//   - (min_uses, max_uses) for param 0 = (1, 1)
//   - Linear rule: max != 0 ✓, min != 0 ✓, max ≤ 1 ✓ → no error
//   - Result: clean
//
// Expected Rust verdict: clean — verify_from_module returns Ok(()).

#[test]
fn fixture_clean_linear_consumer() {
    let mut b = ModuleBuilder::new();
    let t = b.add_type(vec![ValType::I32], vec![]);
    b.add_function(
        t,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    let bytes = b.finish();
    assert!(verify_from_module(&bytes).is_ok());
}

// ----------------------------------------------------------------------
// Fixture 2 — Duplicated Linear (intra-function)
// ----------------------------------------------------------------------
//
// Conceptual AffineScript (rejected by AS source-level QTT checker,
// but valuable as a regression target for the post-codegen verifier
// catching codegen bugs):
//
//     fn dup(s: own String): String = (s, s).0   // hypothetical
//
// Wasm body loads param 0 twice.
//
// Expected OCaml verdict: (1, 2) — max > 1 ⇒
//   LinearUsedMultiple { func_idx = 0, param_idx = 0, count = 2 }
//
// Expected Rust verdict: same.

#[test]
fn fixture_duplicated_linear() {
    let mut b = ModuleBuilder::new();
    let t = b.add_type(vec![ValType::I32], vec![ValType::I32]);
    b.add_function(
        t,
        &[
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
        ],
        vec![OwnershipKind::Linear],
    );
    let bytes = b.finish();
    match verify_from_module(&bytes) {
        Err(VerifyError::Ownership(errs)) => {
            assert!(matches!(
                errs.as_slice(),
                [OwnershipError::LinearUsedMultiple {
                    func_idx: 0,
                    param_idx: 0,
                    count: 2
                }]
            ));
        }
        other => panic!("expected LinearUsedMultiple, got {:?}", other),
    }
}

// ----------------------------------------------------------------------
// Fixture 3 — Dropped Linear on else path
// ----------------------------------------------------------------------
//
// Conceptual AffineScript:
//
//     fn maybe_consume(s: own String, take: i32): unit =
//       if (take != 0) drop s else ()       // s leaks on the else path
//
// Wasm: if (local 1) { local.get 0; drop } end
//
// Expected OCaml verdict:
//   - count_uses_range over (lg1, if(then=[lg0;drop], else=[])) for
//     param 0: outer fold processes If contribution.
//     If's then-arm: (1, 1). Else-arm: (0, 0). Implicit-else absent →
//     IfThen collapse rule: (min(1,0), max(1,0)) = (0, 1).
//   - Linear rule: max ≥ 1, min = 0 ⇒ LinearDroppedOnSomePath.
//
// Expected Rust verdict: same.

#[test]
fn fixture_dropped_linear_in_else() {
    let mut b = ModuleBuilder::new();
    let t = b.add_type(vec![ValType::I32, ValType::I32], vec![]);
    b.add_function(
        t,
        &[
            Instruction::LocalGet(1),
            Instruction::If(BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End,
        ],
        vec![OwnershipKind::Linear, OwnershipKind::Unrestricted],
    );
    let bytes = b.finish();
    match verify_from_module(&bytes) {
        Err(VerifyError::Ownership(errs)) => {
            assert!(matches!(
                errs.as_slice(),
                [OwnershipError::LinearDroppedOnSomePath {
                    func_idx: 0,
                    param_idx: 0
                }]
            ));
        }
        other => panic!("expected LinearDroppedOnSomePath, got {:?}", other),
    }
}

// ----------------------------------------------------------------------
// Fixture 4 — Aliased ExclBorrow
// ----------------------------------------------------------------------
//
// Conceptual AffineScript:
//
//     fn double_borrow(b: mut Buffer): i32 =
//       b.len() + b.len()        // hypothetical — AS QTT would reject
//
// Wasm: loads param 0 twice.
//
// Expected OCaml verdict:
//   - param kind = ExclBorrow
//   - count_uses_range = (2, 2)
//   - ExclBorrow rule: max > 1 ⇒
//     ExclBorrowAliased { func_idx = 0, param_idx = 0, count = 2 }
//
// Expected Rust verdict: same.

#[test]
fn fixture_aliased_excl_borrow() {
    let mut b = ModuleBuilder::new();
    let t = b.add_type(vec![ValType::I32], vec![ValType::I32]);
    b.add_function(
        t,
        &[
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
        ],
        vec![OwnershipKind::ExclBorrow],
    );
    let bytes = b.finish();
    match verify_from_module(&bytes) {
        Err(VerifyError::Ownership(errs)) => {
            assert!(matches!(
                errs.as_slice(),
                [OwnershipError::ExclBorrowAliased {
                    func_idx: 0,
                    param_idx: 0,
                    count: 2
                }]
            ));
        }
        other => panic!("expected ExclBorrowAliased, got {:?}", other),
    }
}

// ----------------------------------------------------------------------
// Fixture 5 — Multi-function module with one clean and one buggy fn
// ----------------------------------------------------------------------
//
// Conceptual AffineScript:
//
//     fn ok(s: own String): unit = drop s
//     fn bad(t: own String): String = t + t      // duplicates t
//
// Expected OCaml verdict (verify_module folds errors across all
// functions): single LinearUsedMultiple for fn 1 param 0.
//
// Expected Rust verdict: same.

#[test]
fn fixture_multi_function_one_buggy() {
    let mut b = ModuleBuilder::new();
    let t_unit = b.add_type(vec![ValType::I32], vec![]);
    let t_ret = b.add_type(vec![ValType::I32], vec![ValType::I32]);
    b.add_function(
        t_unit,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    b.add_function(
        t_ret,
        &[
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
        ],
        vec![OwnershipKind::Linear],
    );
    let bytes = b.finish();
    match verify_from_module(&bytes) {
        Err(VerifyError::Ownership(errs)) => {
            assert_eq!(errs.len(), 1);
            assert!(matches!(
                errs[0],
                OwnershipError::LinearUsedMultiple {
                    func_idx: 1,
                    param_idx: 0,
                    count: 2
                }
            ));
        }
        other => panic!("expected one LinearUsedMultiple on fn 1, got {:?}", other),
    }
}

// ----------------------------------------------------------------------
// Fixture 6 — Cross-module: clean Linear call
// ----------------------------------------------------------------------
//
// Conceptual AffineScript (two compilation units):
//
//     // lib.as
//     pub fn consume(s: own String): unit = drop s
//
//     // app.as
//     import lib::consume
//     fn use_lib(s: own String): unit = consume(s)
//
// Expected OCaml verdict (tw_interface.verify_cross_module):
//   - lib's exported `consume` has Linear param → tracked
//   - app's local fn calls `consume` exactly once on its only path
//   - (min_calls, max_calls) for the import = (1, 1) → no violation
//
// Expected Rust verdict: clean.

#[test]
fn fixture_xmod_clean_linear_call() {
    let mut callee = ModuleBuilder::new();
    let t = callee.add_type(vec![ValType::I32], vec![]);
    let consume_idx = callee.add_function(
        t,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    callee.export_function("consume", consume_idx);
    let callee_bytes = callee.finish();
    let iface = extract_exports(&callee_bytes).unwrap();

    let mut caller = ModuleBuilder::new();
    let t = caller.add_type(vec![ValType::I32], vec![]);
    caller.add_import("lib", "consume", t);
    caller.add_function(
        t,
        &[Instruction::LocalGet(0), Instruction::Call(0)],
        vec![OwnershipKind::Linear],
    );
    let caller_bytes = caller.finish();

    assert!(verify_cross_module(&iface, &caller_bytes).is_ok());
}

// ----------------------------------------------------------------------
// Fixture 7 — Cross-module: Linear import called twice
// ----------------------------------------------------------------------
//
// Conceptual AffineScript:
//
//     // app.as
//     import lib::consume
//     fn double_call(s: own String): unit = consume(s); consume(s)
//     // ^^^ rejected by AS QTT but valuable as codegen-bug catch
//
// Expected OCaml verdict:
//   - max_calls on import slot 0 = 2 ⇒
//     LinearImportCalledMultiple { count = 2 }
//   - caller_func_idx = import_count(1) + local_idx(0) = 1
//
// Expected Rust verdict: same.

#[test]
fn fixture_xmod_linear_called_twice() {
    let mut callee = ModuleBuilder::new();
    let t = callee.add_type(vec![ValType::I32], vec![]);
    let consume_idx = callee.add_function(
        t,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    callee.export_function("consume", consume_idx);
    let callee_bytes = callee.finish();
    let iface = extract_exports(&callee_bytes).unwrap();

    let mut caller = ModuleBuilder::new();
    let t = caller.add_type(vec![ValType::I32], vec![]);
    caller.add_import("lib", "consume", t);
    caller.add_function(
        t,
        &[
            Instruction::LocalGet(0),
            Instruction::Call(0),
            Instruction::LocalGet(0),
            Instruction::Call(0),
        ],
        vec![OwnershipKind::Linear],
    );
    let caller_bytes = caller.finish();

    match verify_cross_module(&iface, &caller_bytes) {
        Err(VerifyError::Cross(errs)) => {
            assert!(matches!(
                errs.as_slice(),
                [CrossError::LinearImportCalledMultiple {
                    caller_func_idx: 1,
                    import_func_idx: 0,
                    count: 2,
                    ..
                }]
            ));
        }
        other => panic!("expected LinearImportCalledMultiple, got {:?}", other),
    }
}

// ----------------------------------------------------------------------
// Fixture 8 — Cross-module: mixed-correctness caller
// ----------------------------------------------------------------------
//
// Conceptual AffineScript: caller has three functions, only one
// misuses the Linear import.
//
//     // app.as
//     import lib::consume
//     fn ok(s: own String): unit = consume(s)            // clean
//     fn unrelated(x: i32): i32 = x + 1                  // doesn't call consume
//     fn bad(s: own String): unit = consume(s); consume(s) // dup
//
// Expected OCaml verdict:
//   - fn 0 (ok)        — max_calls = 1 on import 0 → clean
//   - fn 1 (unrelated) — max_calls = 0 on import 0 → skipped (no obligation)
//   - fn 2 (bad)       — max_calls = 2 on import 0 → LinearImportCalledMultiple
//   - caller_func_idx for fn 2 = import_count(1) + local_idx(2) = 3
//
// Expected Rust verdict: single LinearImportCalledMultiple on caller_func_idx=3.

#[test]
fn fixture_xmod_mixed_correctness() {
    let mut callee = ModuleBuilder::new();
    let t = callee.add_type(vec![ValType::I32], vec![]);
    let consume_idx = callee.add_function(
        t,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    callee.export_function("consume", consume_idx);
    let callee_bytes = callee.finish();
    let iface = extract_exports(&callee_bytes).unwrap();

    let mut caller = ModuleBuilder::new();
    let t_consume = caller.add_type(vec![ValType::I32], vec![]);
    let t_int = caller.add_type(vec![ValType::I32], vec![ValType::I32]);
    caller.add_import("lib", "consume", t_consume);
    caller.add_function(
        t_consume,
        &[Instruction::LocalGet(0), Instruction::Call(0)],
        vec![OwnershipKind::Linear],
    );
    caller.add_function(
        t_int,
        &[
            Instruction::LocalGet(0),
            Instruction::I32Const(1),
            Instruction::I32Add,
        ],
        vec![OwnershipKind::Unrestricted],
    );
    caller.add_function(
        t_consume,
        &[
            Instruction::LocalGet(0),
            Instruction::Call(0),
            Instruction::LocalGet(0),
            Instruction::Call(0),
        ],
        vec![OwnershipKind::Linear],
    );
    let caller_bytes = caller.finish();

    match verify_cross_module(&iface, &caller_bytes) {
        Err(VerifyError::Cross(errs)) => {
            assert_eq!(errs.len(), 1);
            assert!(matches!(
                errs[0],
                CrossError::LinearImportCalledMultiple {
                    caller_func_idx: 3,
                    import_func_idx: 0,
                    count: 2,
                    ..
                }
            ));
        }
        other => panic!("expected one LinearImportCalledMultiple, got {:?}", other),
    }
}

// ----------------------------------------------------------------------
// Fixture 9 — Sanity round-trip: extract_exports + ownership section
// ----------------------------------------------------------------------
//
// Builds a module with three exports of varying ownership shapes:
//   - "consume_string"      (own String)         → param_kinds = [Linear]
//   - "borrow_buffer_mut"   (mut Buffer)         → param_kinds = [ExclBorrow]
//   - "read_count"          (val i32)            → param_kinds = [Unrestricted]
//
// Expected OCaml verdict (tw_interface.extract_exports):
//   - Returns three FuncInterface records, indexed by their global
//     func idx, with the correct param_kinds and ret = Unrestricted.
//
// Expected Rust verdict: same.

#[test]
fn fixture_extract_exports_three_shapes() {
    let mut b = ModuleBuilder::new();
    let t_unit = b.add_type(vec![ValType::I32], vec![]);
    let t_int = b.add_type(vec![ValType::I32], vec![ValType::I32]);

    let consume_idx = b.add_function(
        t_unit,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    b.export_function("consume_string", consume_idx);

    let borrow_idx = b.add_function(
        t_int,
        &[Instruction::LocalGet(0)],
        vec![OwnershipKind::ExclBorrow],
    );
    b.export_function("borrow_buffer_mut", borrow_idx);

    let read_idx = b.add_function(
        t_int,
        &[Instruction::LocalGet(0)],
        vec![OwnershipKind::Unrestricted],
    );
    b.export_function("read_count", read_idx);

    let bytes = b.finish();
    let ifaces = extract_exports(&bytes).unwrap();
    assert_eq!(ifaces.len(), 3);

    let by_name: std::collections::HashMap<&str, &OwnershipKind> = ifaces
        .iter()
        .map(|fi| (fi.name.as_str(), fi.param_kinds.first().unwrap()))
        .collect();
    assert_eq!(by_name["consume_string"], &OwnershipKind::Linear);
    assert_eq!(by_name["borrow_buffer_mut"], &OwnershipKind::ExclBorrow);
    assert_eq!(by_name["read_count"], &OwnershipKind::Unrestricted);
    for fi in &ifaces {
        assert_eq!(fi.ret_kind, OwnershipKind::Unrestricted);
    }
}

// ----------------------------------------------------------------------
// Fixture 10 — Module-wide pass on a realistic shape (no violations)
// ----------------------------------------------------------------------
//
// A small module that exercises:
//   - One Linear param consumed exactly once (good)
//   - One ExclBorrow param read exactly once (good)
//   - One Unrestricted param used multiple times (allowed)
//   - One function with no ownership annotation at all (not in section)
//
// Expected OCaml verdict: clean across all four functions.
// Expected Rust verdict: clean.

#[test]
fn fixture_realistic_clean_module() {
    let mut b = ModuleBuilder::new();
    let t1 = b.add_type(vec![ValType::I32], vec![]);
    let t2 = b.add_type(vec![ValType::I32], vec![ValType::I32]);

    b.add_function(
        t1,
        &[Instruction::LocalGet(0), Instruction::Drop],
        vec![OwnershipKind::Linear],
    );
    b.add_function(
        t2,
        &[Instruction::LocalGet(0)],
        vec![OwnershipKind::ExclBorrow],
    );
    b.add_function(
        t2,
        &[
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
            Instruction::I32Add,
        ],
        vec![OwnershipKind::Unrestricted],
    );
    // Unannotated function: not in the ownership section, so the
    // verifier treats it as unconstrained.
    b.add_function(t2, &[Instruction::LocalGet(0)], vec![]);

    let bytes = b.finish();
    assert!(verify_from_module(&bytes).is_ok());
}
