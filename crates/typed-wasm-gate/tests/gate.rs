// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Load-time enforcement: honest modules gate + instantiate + RUN;
// violating modules are refused BEFORE any runtime sees them. The
// producer inputs come from the real front-end (parse .twasm source →
// emit), so this is the whole pipeline: source → bytes → gate →
// instantiate → execute.

#![cfg(feature = "wasmi-runtime")]

use typed_wasm_codegen::{emit, parser, Op};
use typed_wasm_gate::{gate_link_graph, gate_module, wasmi_runtime::instantiate_verified, GateError};
use wasmi::{Engine, Linker, Store, TypedFunc};

const EX03: &str = include_str!("../../../examples/03-ownership-linearity.twasm");
const GAME: &str = include_str!("../../typed-wasm-codegen/tests/fixtures/multimodule/game.twasm");
const ZIG_DOUBLE: &[u8] =
    include_bytes!("../../typed-wasm-verify/tests/fixtures/zig_producer/zig_double_use.wasm");

/// The honest example-03 module passes the gate and actually runs.
#[test]
fn honest_module_gates_and_executes() {
    let module_ir = parser::parse_module(EX03).expect("ex03 parses");
    let bytes = emit(&module_ir);

    let verified = gate_module(&bytes).expect("honest module must pass the gate");
    assert!(verified.report().typed_sites_checked > 0, "gate checked real pinned sites");

    let engine = Engine::default();
    let mut store = Store::new(&engine, ());
    let linker = <Linker<()>>::new(&engine);
    let instance =
        instantiate_verified(&engine, &mut store, &linker, &verified).expect("instantiates");

    // Run a lowered body end-to-end: read_particle_pos on zeroed memory.
    let read_pos: TypedFunc<(i32,), f32> =
        instance.get_typed_func(&store, "read_particle_pos").unwrap();
    assert_eq!(read_pos.call(&mut store, (0,)).unwrap(), 0.0);
}

/// A double-free mutant is refused at the gate — there is no way to
/// hand it to `instantiate_verified` at all (the witness type never
/// exists), which is the enforcement property.
#[test]
fn double_free_mutant_is_refused_at_the_gate() {
    let mut module_ir = parser::parse_module(EX03).expect("ex03 parses");
    let despawn = module_ir
        .funcs
        .iter()
        .position(|f| f.name == "despawn_particle")
        .unwrap();
    module_ir.funcs[despawn].body =
        vec![Op::LocalGet(0), Op::Drop, Op::LocalGet(0), Op::Drop];
    module_ir.funcs[despawn].locals.clear();
    module_ir.funcs[despawn].accesses.clear();
    let bytes = emit(&module_ir);

    match gate_module(&bytes) {
        Err(GateError::Ownership(_)) => {}
        other => panic!("double-free must be refused at the gate: {other:?}"),
    }
}

/// A foreign producer's violating module (the Zig double-use fixture)
/// is refused the same way — the gate is producer-neutral.
#[test]
fn foreign_producer_violation_is_refused() {
    assert!(matches!(
        gate_module(ZIG_DOUBLE),
        Err(GateError::Ownership(_))
    ));
}

/// Whole-graph gating: the split game modules pass with certificates
/// attached to the consumers; a schema-mutant graph is refused.
#[test]
fn link_graph_gates_with_certificates_and_refuses_mutants() {
    let modules = parser::parse_modules(GAME).expect("game.twasm parses");
    let built: Vec<(String, Vec<u8>)> =
        modules.iter().map(|(n, m)| (n.clone(), emit(m))).collect();
    let graph: Vec<(&str, &[u8])> =
        built.iter().map(|(n, b)| (n.as_str(), b.as_slice())).collect();

    let gated = gate_link_graph(&graph).expect("clean graph passes");
    let ai = &gated.iter().find(|(n, _)| n == "ai").unwrap().1;
    assert_eq!(ai.report().certificates.len(), 1);
    assert_eq!(ai.report().certificates[0].producer, "physics");

    // Mutant: ai expects a type the producer does not export.
    let mut mutant = parser::parse_modules(GAME).unwrap();
    mutant[1].1.region_imports[0]
        .expected_fields
        .iter_mut()
        .find(|f| f.name == "flags")
        .unwrap()
        .wasm_ty = typed_wasm_verify::WasmTy::F64;
    let built: Vec<(String, Vec<u8>)> =
        mutant.iter().map(|(n, m)| (n.clone(), emit(m))).collect();
    let graph: Vec<(&str, &[u8])> =
        built.iter().map(|(n, b)| (n.as_str(), b.as_slice())).collect();
    assert!(matches!(
        gate_link_graph(&graph),
        Err(GateError::RegionImports(_))
    ));
}
