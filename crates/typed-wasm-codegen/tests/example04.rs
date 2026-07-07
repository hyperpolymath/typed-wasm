// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Statement-lowering coverage (ADR-0006 debt: `let`, assignment,
// `if`/`else`, `while`, indexed access, `cast`) — the increment that
// takes examples 03/04 ECS-style system bodies from representative
// stubs to REAL typed loads/stores with pinned access sites, plus a
// wasmi execution gate proving the lowered control flow COMPUTES the
// intended semantics (not merely that it validates).

use typed_wasm_codegen::{emit, parser};
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_access_typing_from_module, verify_from_module,
};
use wasmi::{Engine, Linker, Module as WasmiModule, Store, TypedFunc};

const EX04: &str = include_str!("../../../examples/04-ecs-game.twasm");
const EX03: &str = include_str!("../../../examples/03-ownership-linearity.twasm");

/// example-04's ECS system bodies (while + indexed get/set + if/else +
/// cast + compound f32 expressions) must lower for real: pinned access
/// sites, not the stub's empty access list.
#[test]
fn example04_system_bodies_lower_for_real() {
    let module = parser::parse_module(EX04).expect("04-ecs-game.twasm must parse");

    let sites = |name: &str| {
        let f = module
            .funcs
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("function {name} must be parsed"));
        (f.accesses.len(), f.accesses.iter().filter(|a| a.instr_index.is_some()).count())
    };

    let (total, pinned) = sites("movement_system");
    assert!(total >= 3, "movement_system: expected >=3 access sites, got {total}");
    assert_eq!(total, pinned, "movement_system: every site must be pinned");

    let (total, pinned) = sites("health_regen_system");
    assert!(total >= 4, "health_regen_system: expected >=4 access sites, got {total}");
    assert_eq!(total, pinned, "health_regen_system: every site must be pinned");
}

/// example-03's update_particle (multi-get/set + early return) must
/// also graduate from the stub.
#[test]
fn example03_update_particle_lowers_for_real() {
    let module = parser::parse_module(EX03).expect("03-ownership-linearity.twasm must parse");
    let f = module
        .funcs
        .iter()
        .find(|f| f.name == "update_particle")
        .expect("update_particle must be parsed");
    assert!(
        f.accesses.len() >= 8,
        "update_particle reads 5 fields and writes 4: got {} sites",
        f.accesses.len()
    );
    assert!(f.accesses.iter().all(|a| a.instr_index.is_some()));
}

/// The full verifier stack accepts the real-lowered examples: structural
/// validation, L7/L10 ownership, L2 bounds AND L2 access-typing (every
/// pinned instruction is the right op at the right offset).
#[test]
fn real_lowered_examples_pass_all_verifier_passes() {
    for (name, src) in [("03", EX03), ("04", EX04)] {
        let module = parser::parse_module(src).unwrap_or_else(|e| panic!("ex{name}: {e}"));
        let bytes = emit(&module);
        wasmparser::Validator::new()
            .validate_all(&bytes)
            .unwrap_or_else(|e| panic!("ex{name} must validate: {e}"));
        verify_from_module(&bytes).unwrap_or_else(|e| panic!("ex{name} L7/L10: {e}"));
        let bounds = verify_access_sites_from_module(&bytes).unwrap();
        assert!(bounds.is_empty(), "ex{name} L2 bounds: {bounds:?}");
        let typing = verify_access_typing_from_module(&bytes).unwrap();
        assert!(
            typing.errors.is_empty(),
            "ex{name} L2 access-typing: {:?}",
            typing.errors
        );
    }
}

/// Execution gate for the NEW lowering constructs: while-loops, if/else
/// branches, indexed region access, assignment, and cast<> must COMPUTE
/// correctly in a real engine, not merely validate.
const CELLS: &str = r#"
    region Cell {
        v: i32;
    }
    memory mem { initial: 1; }

    fn set_v(p: &mut region<Cell>, i: i32, v: i32) {
        region.set $p[i] .v, v;
    }

    fn sum_abs(p: &region<Cell>, count: i32) -> i32 {
        let mut acc: i32 = 0;
        let mut i: i32 = 0;
        while i < count {
            region.get $p[i] .v -> x;
            if x > 0 {
                acc = acc + x;
            } else {
                acc = acc - x;
            }
            i = i + 1;
        }
        return acc;
    }

    fn scale(p: &mut region<Cell>, count: i32, k: f32) {
        let mut i: i32 = 0;
        while i < count {
            region.get $p[i] .v -> x;
            region.set $p[i] .v, cast<i32>(cast<f32>(x) * k);
            i = i + 1;
        }
    }
"#;

#[test]
fn lowered_control_flow_executes_with_correct_semantics() {
    let module_ir = parser::parse_module(CELLS).expect("Cells fixture must parse");

    // The fixture must NOT be stub-lowered — the whole point.
    for name in ["set_v", "sum_abs", "scale"] {
        let f = module_ir.funcs.iter().find(|f| f.name == name).unwrap();
        assert!(
            !f.accesses.is_empty(),
            "{name} must lower for real (stub would have no access sites)"
        );
    }

    let bytes = emit(&module_ir);
    let engine = Engine::default();
    let module = WasmiModule::new(&engine, &bytes[..]).expect("loads into wasmi");
    let mut store = Store::new(&engine, ());
    let linker = <Linker<()>>::new(&engine);
    let instance = linker
        .instantiate_and_start(&mut store, &module)
        .expect("instantiate");

    let set_v: TypedFunc<(i32, i32, i32), ()> =
        instance.get_typed_func(&store, "set_v").unwrap();
    let sum_abs: TypedFunc<(i32, i32), i32> =
        instance.get_typed_func(&store, "sum_abs").unwrap();
    let scale: TypedFunc<(i32, i32, f32), ()> =
        instance.get_typed_func(&store, "scale").unwrap();

    const BASE: i32 = 0;
    // cells = [3, -4, 5]
    set_v.call(&mut store, (BASE, 0, 3)).unwrap();
    set_v.call(&mut store, (BASE, 1, -4)).unwrap();
    set_v.call(&mut store, (BASE, 2, 5)).unwrap();

    // |3| + |-4| + |5| — exercises both if-branches and the loop.
    assert_eq!(sum_abs.call(&mut store, (BASE, 3)).unwrap(), 12);
    // A count of 0 must skip the loop entirely.
    assert_eq!(sum_abs.call(&mut store, (BASE, 0)).unwrap(), 0);

    // scale ×2 via f32 round-trip: [6, -8, 10].
    scale.call(&mut store, (BASE, 3, 2.0)).unwrap();
    assert_eq!(sum_abs.call(&mut store, (BASE, 3)).unwrap(), 24);
}
