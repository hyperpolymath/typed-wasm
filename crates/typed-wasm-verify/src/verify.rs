// SPDX-License-Identifier: MPL-2.0
//
// Intra-function L7+L10 verifier.
//
// Rust port of `Tw_verify.count_uses_range` + `verify_function` +
// `verify_from_module` from hyperpolymath/affinescript/lib/tw_verify.ml.
//
// The OCaml original walks an in-memory instruction tree recursively.
// wasmparser hands us a flat operator stream with structured-control
// delimiters (Block/Loop/If/Else/End), so we run the same per-path
// `(min, max)` algorithm with an explicit control-flow frame stack.
//
// For each control structure:
//   - Block / Loop: a single path; uses inside accumulate into the
//     enclosing frame's running total when the End fires.
//   - If with no Else: implicit (0, 0) else-arm, so the contribution
//     is (min(t_min, 0), max(t_max, 0)) = (0, t_max).
//   - If/Else: contributes (min(t_min, e_min), max(t_max, e_max)).
//
// Then verification rules per ownership kind:
//   - Linear:      exactly once on every path
//   - ExclBorrow:  at most once on any path
//   - Unrestricted / SharedBorrow: unconstrained

use wasmparser::{BinaryReaderError, FunctionBody, Operator, Parser, Payload};

use crate::section::{parse_ownership_section_payload, OwnershipEntry};
use crate::{OwnershipError, OwnershipKind, VerifyError, OWNERSHIP_SECTION_NAME};

// ----------------------------------------------------------------------
// Per-path use-range analysis
// ----------------------------------------------------------------------

/// Frame in the control-flow stack while walking a function body.
///
/// Each frame tracks the running `(min, max)` use-count for the side of
/// the control structure that is currently being scanned. For an `If`
/// before its `Else` (or before `End` if there is no else), that side
/// is the then-arm; after `Else`, it's the else-arm and the then-arm's
/// totals are frozen in `then_min` / `then_max`.
#[derive(Debug)]
enum Frame {
    /// Block, Loop, or the implicit body scope. Single execution path.
    Plain { min: u32, max: u32 },
    /// `If` before any `Else` is seen. Current side = then-arm.
    IfThen { then_min: u32, then_max: u32 },
    /// `If` after `Else`. Then-side totals are frozen; current side = else-arm.
    IfElse {
        then_min: u32,
        then_max: u32,
        else_min: u32,
        else_max: u32,
    },
}

impl Frame {
    /// Add `(m, x)` uses to the frame's currently-active side.
    fn add_uses(&mut self, m: u32, x: u32) {
        match self {
            Frame::Plain { min, max } => {
                *min += m;
                *max += x;
            }
            Frame::IfThen { then_min, then_max } => {
                *then_min += m;
                *then_max += x;
            }
            Frame::IfElse {
                else_min, else_max, ..
            } => {
                *else_min += m;
                *else_max += x;
            }
        }
    }

    /// Collapse this frame's contribution to `(min, max)` as if its
    /// scope just closed.
    fn collapse(&self) -> (u32, u32) {
        match *self {
            Frame::Plain { min, max } => (min, max),
            // No `Else` seen: the else-arm is implicitly empty (0, 0).
            // min(then_min, 0) = 0; max(then_max, 0) = then_max.
            Frame::IfThen { then_max, .. } => (0, then_max),
            Frame::IfElse {
                then_min,
                then_max,
                else_min,
                else_max,
            } => (then_min.min(else_min), then_max.max(else_max)),
        }
    }
}

/// Predicate distinguishing the operator we're counting from everything
/// else. Intra-function L7+L10 (this module) uses `LocalGetOf(local_idx)`;
/// cross-module boundary verification (the `cross` module) uses
/// `CallOf(import_idx)`.
pub(crate) trait OpCounter {
    fn matches(&self, op: &Operator<'_>) -> bool;
}

pub(crate) struct LocalGetOf(pub u32);

impl OpCounter for LocalGetOf {
    fn matches(&self, op: &Operator<'_>) -> bool {
        matches!(op, Operator::LocalGet { local_index } if *local_index == self.0)
    }
}

pub(crate) struct CallOf(pub u32);

impl OpCounter for CallOf {
    fn matches(&self, op: &Operator<'_>) -> bool {
        matches!(op, Operator::Call { function_index } if *function_index == self.0)
    }
}

/// Compute the per-path `(min_uses, max_uses)` count for the operator
/// described by `counter` across a function body's instruction stream.
///
/// Streaming equivalent of OCaml `Tw_verify.count_uses_range`. The body
/// reader must yield every operator in order including the final `End`
/// (which is what `wasmparser::FunctionBody::get_operators_reader`
/// produces).
pub(crate) fn count_op_range<C: OpCounter>(
    body: FunctionBody<'_>,
    counter: &C,
) -> Result<(u32, u32), BinaryReaderError> {
    let mut stack: Vec<Frame> = vec![Frame::Plain { min: 0, max: 0 }];
    let mut final_result: Option<(u32, u32)> = None;

    let reader = body.get_operators_reader()?;
    for op_result in reader {
        let op = op_result?;

        if counter.matches(&op) {
            stack
                .last_mut()
                .expect("frame stack underflow on counted op")
                .add_uses(1, 1);
            continue;
        }

        match op {
            Operator::Block { .. } | Operator::Loop { .. } => {
                stack.push(Frame::Plain { min: 0, max: 0 });
            }
            Operator::If { .. } => {
                stack.push(Frame::IfThen {
                    then_min: 0,
                    then_max: 0,
                });
            }
            Operator::Else => {
                let top = stack.last_mut().expect("frame stack underflow at Else");
                match *top {
                    Frame::IfThen { then_min, then_max } => {
                        *top = Frame::IfElse {
                            then_min,
                            then_max,
                            else_min: 0,
                            else_max: 0,
                        };
                    }
                    _ => unreachable!("Else without matching If"),
                }
            }
            Operator::End => {
                let popped = stack.pop().expect("frame stack underflow at End");
                let (m, x) = popped.collapse();
                if let Some(parent) = stack.last_mut() {
                    parent.add_uses(m, x);
                } else {
                    // Outermost frame just closed: this was the final End
                    // of the function body.
                    final_result = Some((m, x));
                }
            }
            _ => {}
        }
    }

    // wasmparser emits the function-body terminating End as part of the
    // operator stream, so `final_result` is normally set when the loop
    // exits. If a fixture omits that End (synthetic / malformed input),
    // fall back to the bottom-frame accumulator so we still produce a
    // total.
    if let Some(r) = final_result {
        Ok(r)
    } else {
        Ok(stack
            .into_iter()
            .next()
            .map(|f| f.collapse())
            .unwrap_or((0, 0)))
    }
}

/// Compute the per-path `(min, max)` count for `local_get local_idx`
/// across a function body. Convenience wrapper around `count_op_range`
/// for the L7+L10 intra-function checks.
pub fn count_uses_range(
    body: FunctionBody<'_>,
    local_idx: u32,
) -> Result<(u32, u32), BinaryReaderError> {
    count_op_range(body, &LocalGetOf(local_idx))
}

// ----------------------------------------------------------------------
// Per-function verification
// ----------------------------------------------------------------------

/// Verify the L7+L10 ownership constraints on a single function body.
/// Returns every violation found; an empty result means the function
/// is clean for its declared param kinds.
///
/// Rust port of OCaml `Tw_verify.verify_function`.
pub fn verify_function(
    body: FunctionBody<'_>,
    param_kinds: &[OwnershipKind],
    func_idx: u32,
) -> Result<Vec<OwnershipError>, BinaryReaderError> {
    let mut errors = Vec::new();
    for (param_idx, kind) in param_kinds.iter().enumerate() {
        let param_idx = param_idx as u32;
        // get_operators_reader takes the body by reference internally but
        // FunctionBody is `Copy`, so cloning is cheap.
        let (min_uses, max_uses) = count_uses_range(body.clone(), param_idx)?;
        match kind {
            OwnershipKind::Linear => {
                if max_uses == 0 {
                    errors.push(OwnershipError::LinearNotUsed {
                        func_idx,
                        param_idx,
                    });
                } else if min_uses == 0 {
                    errors.push(OwnershipError::LinearDroppedOnSomePath {
                        func_idx,
                        param_idx,
                    });
                }
                if max_uses > 1 {
                    errors.push(OwnershipError::LinearUsedMultiple {
                        func_idx,
                        param_idx,
                        count: max_uses,
                    });
                }
            }
            OwnershipKind::ExclBorrow => {
                if max_uses > 1 {
                    errors.push(OwnershipError::ExclBorrowAliased {
                        func_idx,
                        param_idx,
                        count: max_uses,
                    });
                }
            }
            OwnershipKind::Unrestricted | OwnershipKind::SharedBorrow => {}
        }
    }
    Ok(errors)
}

// ----------------------------------------------------------------------
// Module-level entry
// ----------------------------------------------------------------------

/// Verify the L7+L10 ownership constraints across an entire wasm
/// module by reading its embedded `typedwasm.ownership` custom
/// section. Modules without the section verify trivially.
///
/// Rust port of OCaml `Tw_verify.verify_from_module`.
pub fn verify_from_module(wasm_bytes: &[u8]) -> Result<(), VerifyError> {
    // First pass: locate the ownership section (if any) and collect
    // every function body alongside its global function index.
    let mut ownership_payload: Option<Vec<u8>> = None;
    let mut bodies: Vec<FunctionBody<'_>> = Vec::new();
    let mut import_count: u32 = 0;
    // L13 module-isolation (negative form): a module that owns linear
    // memory yet imports a memory/table has a cross-module shared-state
    // channel outside the declared function-import boundary. Mirrors
    // OCaml `Tw_verify.verify_module_isolation` (affinescript PR #280,
    // issue #35). Carrier-free — standard import/memory sections only.
    let mut imported_shared: Option<String> = None;
    let mut has_own_memory = false;

    let parser = Parser::new(0);
    for payload in parser.parse_all(wasm_bytes) {
        match payload? {
            Payload::ImportSection(reader) => {
                // We need import_count to translate global func indices
                // (used in the ownership section) to body indices.
                // wasmparser yields imports of every kind; filter to functions.
                // `.into_imports()` flattens the 0.250 `Imports` group enum
                // back to individual `Import` values.
                for import in reader.into_imports() {
                    let import = import?;
                    match import.ty {
                        wasmparser::TypeRef::Func(_) => import_count += 1,
                        wasmparser::TypeRef::Memory(_) if imported_shared.is_none() => {
                            imported_shared = Some(format!(
                                "module owns linear memory yet imports \
                                 memory '{}.{}' (cross-module shared memory \
                                 breaks L13 isolation)",
                                import.module, import.name
                            ));
                        }
                        wasmparser::TypeRef::Table(_) if imported_shared.is_none() => {
                            imported_shared = Some(format!(
                                "module owns linear memory yet imports table \
                                 '{}.{}' (externally-backed table breaks L13 \
                                 isolation)",
                                import.module, import.name
                            ));
                        }
                        _ => {}
                    }
                }
            }
            Payload::MemorySection(reader) => {
                if reader.count() > 0 {
                    has_own_memory = true;
                }
            }
            Payload::CustomSection(reader) if reader.name() == OWNERSHIP_SECTION_NAME => {
                ownership_payload = Some(reader.data().to_vec());
            }
            Payload::CodeSectionEntry(body) => {
                bodies.push(body);
            }
            _ => {}
        }
    }

    let Some(payload) = ownership_payload else {
        // No ownership section: nothing constrained, verify trivially.
        return Ok(());
    };
    let entries = parse_ownership_section_payload(&payload);

    let mut all_errors = Vec::new();

    // L13 module isolation, gated behind the ownership section just
    // like the OCaml port (preserves "no section ⇒ Ok").
    if has_own_memory {
        if let Some(reason) = imported_shared {
            all_errors.push(OwnershipError::ModuleNotIsolated { reason });
        }
    }

    for OwnershipEntry {
        func_idx,
        param_kinds,
        ..
    } in entries
    {
        // Global func index → body index: skip imports.
        let Some(body_idx) = func_idx.checked_sub(import_count) else {
            // Imported function: no body to inspect (the import's host
            // implementation is opaque). Matches OCaml's
            // `local_idx < 0` short-circuit.
            continue;
        };
        let body_idx = body_idx as usize;
        if body_idx >= bodies.len() {
            // Entry refers to a function we never saw (malformed module
            // or section). Skip silently — matches OCaml's
            // `local_idx >= List.length funcs` short-circuit.
            continue;
        }
        let errs = verify_function(bodies[body_idx].clone(), &param_kinds, func_idx)?;
        all_errors.extend(errs);
    }

    if all_errors.is_empty() {
        Ok(())
    } else {
        Err(VerifyError::Ownership(all_errors))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::section::build_ownership_section_payload;
    use crate::OwnershipEntry;
    use wasm_encoder::{
        CodeSection, CustomSection, Function, FunctionSection, ImportSection, Instruction, Module,
        TypeSection, ValType,
    };

    /// Build a single-function wasm module with the given function body
    /// (as a sequence of instructions, NOT including the trailing `End`
    /// — `wasm_encoder::Function` adds it automatically). The function
    /// has `n_params` i32 params, no return value.
    ///
    /// Optionally embeds an `typedwasm.ownership` custom section
    /// claiming the function (at global index 0, since there are no
    /// imports) has the given param kinds.
    fn module_with_body(
        n_params: u32,
        body: &[Instruction<'_>],
        ownership: Option<Vec<OwnershipKind>>,
    ) -> Vec<u8> {
        let mut module = Module::new();

        let mut types = TypeSection::new();
        types
            .ty()
            .function((0..n_params).map(|_| ValType::I32), [ValType::I32]);
        module.section(&types);

        let mut funcs = FunctionSection::new();
        funcs.function(0);
        module.section(&funcs);

        let mut code = CodeSection::new();
        let mut f = Function::new([]);
        for instr in body {
            f.instruction(instr);
        }
        // Must end with the body's trailing End for valid wasm; do not
        // double up here — `wasm_encoder::Function` documents this
        // requirement.
        f.instruction(&Instruction::End);
        code.function(&f);
        module.section(&code);

        if let Some(kinds) = ownership {
            let payload = build_ownership_section_payload(&[OwnershipEntry {
                func_idx: 0,
                param_kinds: kinds,
                ret_kind: OwnershipKind::Unrestricted,
            }]);
            let custom = CustomSection {
                name: OWNERSHIP_SECTION_NAME.into(),
                data: payload.as_slice().into(),
            };
            module.section(&custom);
        }

        module.finish()
    }

    // ------------------------------------------------------------------
    // count_uses_range — the algorithmic core
    // ------------------------------------------------------------------

    /// Return the (min, max) range for `local_idx` across a body built
    /// from `body` (instructions; trailing `End` added by the helper).
    fn range_in(body: &[Instruction<'_>], local_idx: u32) -> (u32, u32) {
        let wasm = module_with_body(2, body, None);
        let parser = Parser::new(0);
        for payload in parser.parse_all(&wasm) {
            if let Payload::CodeSectionEntry(body) = payload.unwrap() {
                return count_uses_range(body, local_idx).unwrap();
            }
        }
        panic!("no code section entry in synthetic module")
    }

    #[test]
    fn no_uses() {
        let body = [Instruction::I32Const(0), Instruction::Return];
        assert_eq!(range_in(&body, 0), (0, 0));
    }

    #[test]
    fn one_use() {
        let body = [Instruction::LocalGet(0), Instruction::Return];
        assert_eq!(range_in(&body, 0), (1, 1));
    }

    #[test]
    fn two_uses_same_path() {
        let body = [
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (2, 2));
    }

    #[test]
    fn use_in_both_if_branches() {
        // if (lg1) { lg0 } else { lg0 } — used exactly once on every path
        let body = [
            Instruction::LocalGet(1),
            Instruction::If(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::Else,
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End, // closes If
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (1, 1));
    }

    #[test]
    fn use_in_then_only() {
        // if (lg1) { lg0 } — partial drop: (min=0, max=1)
        let body = [
            Instruction::LocalGet(1),
            Instruction::If(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End,
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (0, 1));
    }

    #[test]
    fn use_twice_in_then_once_in_else() {
        // if (lg1) { lg0; lg0 } else { lg0 } — (min=1, max=2)
        let body = [
            Instruction::LocalGet(1),
            Instruction::If(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::Else,
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End,
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (1, 2));
    }

    #[test]
    fn use_inside_block_passthrough() {
        // block { lg0 } — Block is a single path, so the inner (1,1)
        // propagates as (1,1).
        let body = [
            Instruction::Block(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End,
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (1, 1));
    }

    #[test]
    fn use_inside_loop_passthrough() {
        // loop { lg0 } — Loop is also a single path for this static
        // counter (the analysis does not model iteration).
        let body = [
            Instruction::Loop(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End,
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (1, 1));
    }

    #[test]
    fn nested_if_use_in_inner_then_only() {
        // if (lg1) { if (lg1) { lg0 } } — innermost If is (0, 1), outer
        // also (0, 1) — outer is then-only so the implicit-else rule
        // gives (min(then=0, 0), max(then=1, 0)) = (0, 1).
        let body = [
            Instruction::LocalGet(1),
            Instruction::If(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(1),
            Instruction::If(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End, // inner If
            Instruction::End, // outer If
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        assert_eq!(range_in(&body, 0), (0, 1));
    }

    // ------------------------------------------------------------------
    // verify_from_module — end-to-end
    // ------------------------------------------------------------------

    #[test]
    fn linear_used_exactly_once_is_clean() {
        let body = [Instruction::LocalGet(0), Instruction::Return];
        let wasm = module_with_body(1, &body, Some(vec![OwnershipKind::Linear]));
        assert!(verify_from_module(&wasm).is_ok());
    }

    #[test]
    fn linear_not_used_at_all_errors() {
        let body = [Instruction::I32Const(0), Instruction::Return];
        let wasm = module_with_body(1, &body, Some(vec![OwnershipKind::Linear]));
        match verify_from_module(&wasm) {
            Err(VerifyError::Ownership(errs)) => {
                assert!(matches!(
                    errs.as_slice(),
                    [OwnershipError::LinearNotUsed {
                        func_idx: 0,
                        param_idx: 0
                    }]
                ));
            }
            other => panic!("expected LinearNotUsed, got {:?}", other),
        }
    }

    #[test]
    fn linear_dropped_on_some_path_errors() {
        // if (lg1) { lg0 } — Linear used in then-only.
        let body = [
            Instruction::LocalGet(1),
            Instruction::If(wasm_encoder::BlockType::Empty),
            Instruction::LocalGet(0),
            Instruction::Drop,
            Instruction::End,
            Instruction::I32Const(0),
            Instruction::Return,
        ];
        let wasm = module_with_body(
            2,
            &body,
            Some(vec![OwnershipKind::Linear, OwnershipKind::Unrestricted]),
        );
        match verify_from_module(&wasm) {
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

    #[test]
    fn linear_used_twice_errors() {
        let body = [
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
            Instruction::Return,
        ];
        let wasm = module_with_body(1, &body, Some(vec![OwnershipKind::Linear]));
        match verify_from_module(&wasm) {
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

    #[test]
    fn excl_borrow_used_twice_errors() {
        let body = [
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
            Instruction::Return,
        ];
        let wasm = module_with_body(1, &body, Some(vec![OwnershipKind::ExclBorrow]));
        match verify_from_module(&wasm) {
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

    #[test]
    fn excl_borrow_used_once_is_clean() {
        let body = [Instruction::LocalGet(0), Instruction::Return];
        let wasm = module_with_body(1, &body, Some(vec![OwnershipKind::ExclBorrow]));
        assert!(verify_from_module(&wasm).is_ok());
    }

    #[test]
    fn unrestricted_used_arbitrarily_is_clean() {
        let body = [
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::LocalGet(0),
            Instruction::I32Add,
            Instruction::I32Add,
            Instruction::Return,
        ];
        let wasm = module_with_body(1, &body, Some(vec![OwnershipKind::Unrestricted]));
        assert!(verify_from_module(&wasm).is_ok());
    }

    #[test]
    fn module_without_ownership_section_is_trivially_clean() {
        // No section ⇒ no constraints ⇒ Ok.
        let body = [Instruction::I32Const(0), Instruction::Return];
        let wasm = module_with_body(1, &body, None);
        assert!(verify_from_module(&wasm).is_ok());
    }

    #[test]
    fn empty_module_is_trivially_clean() {
        let module = Module::new().finish();
        assert!(verify_from_module(&module).is_ok());
    }

    // ------------------------------------------------------------------
    // L13 module isolation (negative form) — parity with OCaml
    // Tw_verify.verify_module_isolation (affinescript PR #280, #35).
    // ------------------------------------------------------------------

    /// Module owning its own memory, optionally also importing a memory.
    /// Always carries an (empty) ownership section so the isolation
    /// check is reached (gated behind it, like the OCaml port).
    fn isolation_module(import_memory: bool) -> Vec<u8> {
        use wasm_encoder::{EntityType, MemorySection, MemoryType};
        let mut module = Module::new();

        if import_memory {
            let mut imports = ImportSection::new();
            imports.import(
                "Host",
                "memory",
                EntityType::Memory(MemoryType {
                    minimum: 1,
                    maximum: None,
                    memory64: false,
                    shared: false,
                    page_size_log2: None,
                }),
            );
            module.section(&imports);
        }

        let mut mems = MemorySection::new();
        mems.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        module.section(&mems);

        // count=0 ownership payload — present so verify_from_module
        // does not short-circuit on "no ownership section ⇒ Ok".
        let payload = build_ownership_section_payload(&[]);
        module.section(&CustomSection {
            name: OWNERSHIP_SECTION_NAME.into(),
            data: payload.as_slice().into(),
        });
        module.finish()
    }

    #[test]
    fn isolated_own_memory_module_is_ok() {
        assert!(verify_from_module(&isolation_module(false)).is_ok());
    }

    #[test]
    fn own_memory_plus_imported_memory_violates_l13() {
        match verify_from_module(&isolation_module(true)) {
            Err(VerifyError::Ownership(errs)) => assert!(errs
                .iter()
                .any(|e| matches!(e, OwnershipError::ModuleNotIsolated { .. }))),
            other => panic!("expected ModuleNotIsolated, got {other:?}"),
        }
    }

    #[test]
    fn imported_memory_without_ownership_section_is_ok() {
        // Contract: no ownership section ⇒ Ok even if it would violate.
        use wasm_encoder::{EntityType, MemorySection, MemoryType};
        let mut module = Module::new();
        let mut imports = ImportSection::new();
        imports.import(
            "Host",
            "memory",
            EntityType::Memory(MemoryType {
                minimum: 1,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            }),
        );
        module.section(&imports);
        let mut mems = MemorySection::new();
        mems.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        module.section(&mems);
        assert!(verify_from_module(&module.finish()).is_ok());
    }
}

// ----------------------------------------------------------------------
// L15 capabilities verifier pass (proposal 0001)
// ----------------------------------------------------------------------

#[cfg(feature = "unstable-l15")]
use crate::section::parse_capabilities_section_payload;
#[cfg(feature = "unstable-l15")]
use crate::{CapabilitiesError, CAPABILITIES_SECTION_NAME};

/// Pre-scan the module to discover `(import_count, locally_defined_count)`
/// pairs so cross-section verifiers can compute the total wasm function
/// count without re-parsing the whole module per check.
fn function_count(wasm_bytes: &[u8]) -> Result<u32, VerifyError> {
    let parser = Parser::new(0);
    let mut import_count: u32 = 0;
    let mut local_count: u32 = 0;
    for payload in parser.parse_all(wasm_bytes) {
        match payload? {
            Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    let import = import?;
                    if matches!(import.ty, wasmparser::TypeRef::Func(_)) {
                        import_count += 1;
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                local_count = reader.count();
            }
            _ => {}
        }
    }
    Ok(import_count + local_count)
}

#[cfg(feature = "unstable-l15")]
pub fn verify_capabilities_from_module(
    wasm_bytes: &[u8],
) -> Result<Vec<CapabilitiesError>, VerifyError> {
    // Locate the capabilities custom section.
    let parser = Parser::new(0);
    let mut payload_bytes: Option<Vec<u8>> = None;
    for payload in parser.parse_all(wasm_bytes) {
        if let Payload::CustomSection(reader) = payload? {
            if reader.name() == CAPABILITIES_SECTION_NAME {
                payload_bytes = Some(reader.data().to_vec());
                break;
            }
        }
    }
    let Some(payload) = payload_bytes else {
        // No capabilities section: nothing constrained, verify trivially.
        return Ok(vec![]);
    };
    let Some((capabilities, functions)) = parse_capabilities_section_payload(&payload) else {
        // Unsupported version: lenient — return no errors. Producers
        // emitting a version we don't know are not our problem; they
        // should bump the verifier first.
        return Ok(vec![]);
    };

    let fn_count = function_count(wasm_bytes)?;
    let cap_count = capabilities.len() as u32;
    let mut errors = Vec::new();

    for (entry_idx, fc) in functions.iter().enumerate() {
        let entry_idx = entry_idx as u32;
        if fc.func_idx >= fn_count {
            errors.push(CapabilitiesError::FuncIdxOutOfRange {
                entry_idx,
                func_idx: fc.func_idx,
                function_count: fn_count,
            });
        }
        for &cap_idx in &fc.required {
            if cap_idx >= cap_count {
                errors.push(CapabilitiesError::CapabilityIdxOutOfRange {
                    entry_idx,
                    func_idx: fc.func_idx,
                    cap_idx,
                    capability_count: cap_count,
                });
            }
        }
    }
    Ok(errors)
}

// ----------------------------------------------------------------------
// L2 access-sites verifier pass (proposal 0002)
// ----------------------------------------------------------------------

#[cfg(feature = "unstable-l2")]
use crate::section::{parse_access_sites_section_payload, parse_regions_section_payload};
#[cfg(feature = "unstable-l2")]
use crate::{AccessSiteError, ACCESS_SITES_SECTION_NAME, REGIONS_SECTION_NAME};

#[cfg(feature = "unstable-l2")]
pub fn verify_access_sites_from_module(
    wasm_bytes: &[u8],
) -> Result<Vec<AccessSiteError>, VerifyError> {
    // Collect both companion sections in a single pass.
    let parser = Parser::new(0);
    let mut access_sites_payload: Option<Vec<u8>> = None;
    let mut regions_payload: Option<Vec<u8>> = None;
    for payload in parser.parse_all(wasm_bytes) {
        if let Payload::CustomSection(reader) = payload? {
            match reader.name() {
                ACCESS_SITES_SECTION_NAME => {
                    access_sites_payload = Some(reader.data().to_vec());
                }
                REGIONS_SECTION_NAME => {
                    regions_payload = Some(reader.data().to_vec());
                }
                _ => {}
            }
        }
    }
    let Some(access_payload) = access_sites_payload else {
        // No access-sites section: trivially verified. Note that absence
        // of the section means "no claim made about L2 enforcement,"
        // not "claim of compliance" — separate concern.
        return Ok(vec![]);
    };
    // MissingDependentCarrier check (proposal 0002 §"Producer obligations" #2):
    // access-sites without regions is a hard error.
    let Some(regions_bytes) = regions_payload else {
        return Ok(vec![AccessSiteError::MissingDependentRegions]);
    };
    let Some(regions) = parse_regions_section_payload(&regions_bytes) else {
        // Regions section present but unparseable (version mismatch).
        // Treat as missing for MissingDependentCarrier purposes —
        // we can't validate against a table we can't read.
        return Ok(vec![AccessSiteError::MissingDependentRegions]);
    };
    let Some(entries) = parse_access_sites_section_payload(&access_payload) else {
        // Unsupported access-sites version: lenient, no errors.
        return Ok(vec![]);
    };

    let fn_count = function_count(wasm_bytes)?;
    let region_count = regions.len() as u32;
    let mut errors = Vec::new();

    for (entry_idx, e) in entries.iter().enumerate() {
        let entry_idx = entry_idx as u32;
        if e.func_idx >= fn_count {
            errors.push(AccessSiteError::FuncIdxOutOfRange {
                entry_idx,
                func_idx: e.func_idx,
                function_count: fn_count,
            });
        }
        if e.region_id >= region_count {
            errors.push(AccessSiteError::RegionIdOutOfRange {
                entry_idx,
                region_id: e.region_id,
                region_count,
            });
            // If region_id is out of bounds we cannot meaningfully
            // check field_id — skip to next entry.
            continue;
        }
        let field_count = regions[e.region_id as usize].fields.len() as u32;
        if e.field_id >= field_count {
            errors.push(AccessSiteError::FieldIdOutOfRange {
                entry_idx,
                region_id: e.region_id,
                field_id: e.field_id,
                field_count,
            });
        }
    }
    Ok(errors)
}

// ----------------------------------------------------------------------
// Tests — capabilities + access-sites verifier passes
// ----------------------------------------------------------------------

#[cfg(all(test, feature = "unstable-l15"))]
mod capabilities_verifier_tests {
    use super::*;
    use crate::section::{
        build_capabilities_section_payload, CapabilityEntry, FunctionCapabilities,
    };
    use wasm_encoder::{
        CodeSection, CustomSection, Function, FunctionSection, Instruction, Module, TypeSection,
        ValType,
    };

    /// Build a valid wasm module with `n_locals` empty `() -> ()`
    /// functions. wasm validation requires that FunctionSection and
    /// CodeSection have matching counts; this helper enforces that
    /// invariant so tests can focus on the section we're verifying.
    fn module_with_n_funcs(n_locals: u32) -> Module {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types
            .ty()
            .function(Vec::<ValType>::new(), Vec::<ValType>::new());
        module.section(&types);
        let mut funcs = FunctionSection::new();
        for _ in 0..n_locals {
            funcs.function(0);
        }
        module.section(&funcs);
        let mut code = CodeSection::new();
        for _ in 0..n_locals {
            let mut f = Function::new([]);
            f.instruction(&Instruction::End);
            code.function(&f);
        }
        module.section(&code);
        module
    }

    fn empty_module_with_function_section(n_locals: u32) -> Vec<u8> {
        module_with_n_funcs(n_locals).finish()
    }

    fn module_with_capabilities(
        n_locals: u32,
        caps: Vec<CapabilityEntry>,
        funs: Vec<FunctionCapabilities>,
    ) -> Vec<u8> {
        let mut module = module_with_n_funcs(n_locals);
        let payload = build_capabilities_section_payload(&caps, &funs);
        module.section(&CustomSection {
            name: CAPABILITIES_SECTION_NAME.into(),
            data: (&payload[..]).into(),
        });
        module.finish()
    }

    #[test]
    fn module_without_section_verifies_trivially() {
        let bytes = empty_module_with_function_section(2);
        assert_eq!(verify_capabilities_from_module(&bytes).unwrap(), vec![]);
    }

    #[test]
    fn well_formed_capabilities_verifies_clean() {
        let bytes = module_with_capabilities(
            3,
            vec![
                CapabilityEntry { name: "net".into() },
                CapabilityEntry { name: "fs".into() },
            ],
            vec![FunctionCapabilities {
                func_idx: 1,
                required: vec![0],
            }],
        );
        assert_eq!(verify_capabilities_from_module(&bytes).unwrap(), vec![]);
    }

    #[test]
    fn out_of_bounds_func_idx_is_flagged() {
        let bytes = module_with_capabilities(
            2,
            vec![CapabilityEntry { name: "net".into() }],
            vec![FunctionCapabilities {
                func_idx: 99, // module has only 2 functions
                required: vec![0],
            }],
        );
        let errors = verify_capabilities_from_module(&bytes).unwrap();
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            errors[0],
            CapabilitiesError::FuncIdxOutOfRange {
                entry_idx: 0,
                func_idx: 99,
                function_count: 2,
            }
        ));
    }

    #[test]
    fn out_of_bounds_capability_index_is_flagged() {
        let bytes = module_with_capabilities(
            2,
            vec![CapabilityEntry { name: "net".into() }], // 1 capability
            vec![FunctionCapabilities {
                func_idx: 0,
                required: vec![0, 5], // 5 is out of bounds
            }],
        );
        let errors = verify_capabilities_from_module(&bytes).unwrap();
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            errors[0],
            CapabilitiesError::CapabilityIdxOutOfRange {
                entry_idx: 0,
                func_idx: 0,
                cap_idx: 5,
                capability_count: 1,
            }
        ));
    }

    #[test]
    fn imports_count_toward_function_count() {
        use wasm_encoder::{EntityType, ImportSection};
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types
            .ty()
            .function(Vec::<ValType>::new(), Vec::<ValType>::new());
        module.section(&types);
        let mut imports = ImportSection::new();
        imports.import("env", "host", EntityType::Function(0));
        module.section(&imports);
        let mut funcs = FunctionSection::new();
        funcs.function(0); // local func at index 1 (after the 1 import)
        module.section(&funcs);
        let mut code = CodeSection::new();
        let mut f = Function::new([]);
        f.instruction(&Instruction::End);
        code.function(&f);
        module.section(&code);
        let caps = vec![CapabilityEntry { name: "x".into() }];
        let funs = vec![FunctionCapabilities {
            func_idx: 1, // valid: imported = 1, local = 1, total = 2
            required: vec![0],
        }];
        let payload = build_capabilities_section_payload(&caps, &funs);
        module.section(&CustomSection {
            name: CAPABILITIES_SECTION_NAME.into(),
            data: (&payload[..]).into(),
        });
        assert_eq!(
            verify_capabilities_from_module(&module.finish()).unwrap(),
            vec![]
        );
    }
}

#[cfg(all(test, feature = "unstable-l2"))]
mod access_sites_verifier_tests {
    use super::*;
    use crate::section::{
        build_access_sites_section_payload, build_regions_section_payload, AccessSiteEntry,
        FieldEntry, FieldKind, Nullability, RegionEntry, WasmTy, NO_TARGET_REGION,
    };
    use wasm_encoder::{
        CodeSection, CustomSection, Function, FunctionSection, Instruction, Module, TypeSection,
        ValType,
    };

    fn scalar_field(name: &str, ty: WasmTy) -> FieldEntry {
        FieldEntry {
            name: name.into(),
            kind: FieldKind::Scalar,
            wasm_ty: ty,
            target_region: NO_TARGET_REGION,
            nullability: Nullability::NonNull,
            cardinality: 1,
        }
    }

    fn module_with_sections(
        n_locals: u32,
        regions: Option<Vec<RegionEntry>>,
        entries: Option<Vec<AccessSiteEntry>>,
    ) -> Vec<u8> {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types
            .ty()
            .function(Vec::<ValType>::new(), Vec::<ValType>::new());
        module.section(&types);
        let mut funcs = FunctionSection::new();
        for _ in 0..n_locals {
            funcs.function(0);
        }
        module.section(&funcs);
        let mut code = CodeSection::new();
        for _ in 0..n_locals {
            let mut f = Function::new([]);
            f.instruction(&Instruction::End);
            code.function(&f);
        }
        module.section(&code);
        if let Some(regions) = regions {
            let bytes = build_regions_section_payload(&regions);
            module.section(&CustomSection {
                name: REGIONS_SECTION_NAME.into(),
                data: (&bytes[..]).into(),
            });
        }
        if let Some(entries) = entries {
            let bytes = build_access_sites_section_payload(&entries);
            module.section(&CustomSection {
                name: ACCESS_SITES_SECTION_NAME.into(),
                data: (&bytes[..]).into(),
            });
        }
        module.finish()
    }

    #[test]
    fn module_without_access_sites_section_verifies_trivially() {
        let bytes = module_with_sections(2, None, None);
        assert_eq!(verify_access_sites_from_module(&bytes).unwrap(), vec![]);
    }

    #[test]
    fn access_sites_without_regions_is_missing_dependent_carrier() {
        let entries = vec![AccessSiteEntry {
            func_idx: 0,
            instruction_byte_offset: 7,
            region_id: 0,
            field_id: 0,
        }];
        let bytes = module_with_sections(2, None, Some(entries));
        let errors = verify_access_sites_from_module(&bytes).unwrap();
        assert_eq!(errors, vec![AccessSiteError::MissingDependentRegions]);
    }

    #[test]
    fn well_formed_access_sites_verifies_clean() {
        let regions = vec![RegionEntry {
            name: "R".into(),
            fields: vec![scalar_field("f", WasmTy::I32), scalar_field("g", WasmTy::F64)],
            region_byte_size: 12,
        }];
        let entries = vec![AccessSiteEntry {
            func_idx: 0,
            instruction_byte_offset: 7,
            region_id: 0,
            field_id: 1,
        }];
        let bytes = module_with_sections(2, Some(regions), Some(entries));
        assert_eq!(verify_access_sites_from_module(&bytes).unwrap(), vec![]);
    }

    #[test]
    fn out_of_bounds_func_idx_is_flagged() {
        let regions = vec![RegionEntry {
            name: "R".into(),
            fields: vec![scalar_field("f", WasmTy::I32)],
            region_byte_size: 4,
        }];
        let entries = vec![AccessSiteEntry {
            func_idx: 42, // module has 2 funcs
            instruction_byte_offset: 0,
            region_id: 0,
            field_id: 0,
        }];
        let bytes = module_with_sections(2, Some(regions), Some(entries));
        let errors = verify_access_sites_from_module(&bytes).unwrap();
        assert!(matches!(
            errors.as_slice(),
            [AccessSiteError::FuncIdxOutOfRange {
                func_idx: 42,
                function_count: 2,
                ..
            }]
        ));
    }

    #[test]
    fn out_of_bounds_region_id_is_flagged_and_skips_field_check() {
        let regions = vec![RegionEntry {
            name: "R".into(),
            fields: vec![scalar_field("f", WasmTy::I32)],
            region_byte_size: 4,
        }];
        let entries = vec![AccessSiteEntry {
            func_idx: 0,
            instruction_byte_offset: 0,
            region_id: 99, // module has 1 region
            field_id: 99,  // would-be out of bounds, but skipped
        }];
        let bytes = module_with_sections(2, Some(regions), Some(entries));
        let errors = verify_access_sites_from_module(&bytes).unwrap();
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            errors[0],
            AccessSiteError::RegionIdOutOfRange {
                region_id: 99,
                region_count: 1,
                ..
            }
        ));
    }

    #[test]
    fn out_of_bounds_field_id_is_flagged() {
        let regions = vec![RegionEntry {
            name: "R".into(),
            fields: vec![scalar_field("f", WasmTy::I32)],
            region_byte_size: 4,
        }];
        let entries = vec![AccessSiteEntry {
            func_idx: 0,
            instruction_byte_offset: 0,
            region_id: 0,
            field_id: 7, // region R has 1 field
        }];
        let bytes = module_with_sections(2, Some(regions), Some(entries));
        let errors = verify_access_sites_from_module(&bytes).unwrap();
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            errors[0],
            AccessSiteError::FieldIdOutOfRange {
                region_id: 0,
                field_id: 7,
                field_count: 1,
                ..
            }
        ));
    }
}
