// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// `region.scan` closure lowering + `is_null` (v0 null = 0) — the last
// statement forms that previously fell back to representative stubs.
// Scans lower to a bounded loop over the region's declared instances
// with the predicate's bare field idents resolving to typed loads off
// the current-instance address; the closure handle `$e` binds that
// address for the body.

use typed_wasm_codegen::{emit, parser};
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_access_typing_from_module, verify_from_module,
};
use wasmi::{Engine, Linker, Module as WasmiModule, Store, TypedFunc};

const EX01: &str = include_str!("../../../examples/01-single-module.twasm");
const EX02: &str = include_str!("../../../examples/02-multi-module.twasm");

/// The scan-shaped bodies across examples 01/02 lower for real.
#[test]
fn scan_bodies_lower_for_real() {
    let ex01 = parser::parse_module(EX01).expect("ex01 parses");
    let ex02 = parser::parse_module(EX02).expect("ex02 parses");
    for (module, name, min_sites) in [
        (&ex01, "count_active_enemies", 1), // pred load: is_active
        (&ex02, "physics_step", 7),         // pred + 6 gets + 3 sets
        (&ex02, "collect_visible", 1),      // pred load: flags
        (&ex02, "ai_decision", 8),          // opt unwrap + indexed get/set
    ] {
        let f = module
            .funcs
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("{name} must be parsed"));
        assert!(
            f.accesses.len() >= min_sites,
            "{name}: expected >={min_sites} sites, got {}",
            f.accesses.len()
        );
        assert!(
            f.accesses.iter().all(|a| a.instr_index.is_some()),
            "{name}: every site must be pinned"
        );
    }
}

/// Full verifier stack over the scan-lowered examples.
#[test]
fn scan_lowered_examples_pass_all_verifier_passes() {
    for (name, src) in [("01", EX01), ("02", EX02)] {
        let module = parser::parse_module(src).unwrap_or_else(|e| panic!("ex{name}: {e}"));
        let bytes = emit(&module);
        wasmparser::Validator::new()
            .validate_all(&bytes)
            .unwrap_or_else(|e| panic!("ex{name} must validate: {e}"));
        verify_from_module(&bytes).unwrap_or_else(|e| panic!("ex{name} L7/L10: {e}"));
        let bounds = verify_access_sites_from_module(&bytes).unwrap();
        assert!(bounds.is_empty(), "ex{name} L2 bounds: {bounds:?}");
        let typing = verify_access_typing_from_module(&bytes).unwrap();
        assert!(typing.errors.is_empty(), "ex{name} L2 typing: {:?}", typing.errors);
    }
}

/// Execution gate: a where-predicated scan must visit exactly the
/// matching instances, and `is_null` must implement the v0 null = 0
/// convention.
const CELLS: &str = r#"
    region Cell[8] {
        flag: u32;
        v: i32;
    }
    memory mem { initial: 1; }

    fn set_cell(p: &mut region<Cell>, i: i32, flag: u32, v: i32) {
        region.set $p[i] .flag, flag;
        region.set $p[i] .v, v;
    }

    fn sum_flagged(p: &region<Cell>) -> i32 {
        let mut acc: i32 = 0;
        region.scan $p where (flag & 1) == 1 -> |c| {
            region.get $c .v -> x;
            acc = acc + x;
        }
        return acc;
    }

    fn non_null(x: i32) -> i32 {
        if !is_null(x) {
            return 1;
        }
        return 0;
    }
"#;

#[test]
fn scan_and_is_null_execute_with_correct_semantics() {
    let module_ir = parser::parse_module(CELLS).expect("Cells fixture parses");
    for name in ["set_cell", "sum_flagged", "non_null"] {
        let f = module_ir.funcs.iter().find(|f| f.name == name).unwrap();
        assert!(
            name == "non_null" || !f.accesses.is_empty(),
            "{name} must lower for real (stub has no access sites)"
        );
    }

    let bytes = emit(&module_ir);
    let engine = Engine::default();
    let module = WasmiModule::new(&engine, &bytes[..]).expect("loads into wasmi");
    let mut store = Store::new(&engine, ());
    let instance = <Linker<()>>::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .expect("instantiate");

    let set_cell: TypedFunc<(i32, i32, i32, i32), ()> =
        instance.get_typed_func(&store, "set_cell").unwrap();
    let sum_flagged: TypedFunc<(i32,), i32> =
        instance.get_typed_func(&store, "sum_flagged").unwrap();
    let non_null: TypedFunc<(i32,), i32> =
        instance.get_typed_func(&store, "non_null").unwrap();

    const BASE: i32 = 0;
    // Instances 0..3 populated; 4..7 stay zero (flag 0 -> skipped).
    set_cell.call(&mut store, (BASE, 0, 1, 10)).unwrap(); // flagged
    set_cell.call(&mut store, (BASE, 1, 2, 20)).unwrap(); // even flag: skipped
    set_cell.call(&mut store, (BASE, 2, 3, 30)).unwrap(); // flagged (3 & 1 == 1)
    set_cell.call(&mut store, (BASE, 3, 0, 40)).unwrap(); // unflagged: skipped

    assert_eq!(sum_flagged.call(&mut store, (BASE,)).unwrap(), 40, "10 + 30");

    assert_eq!(non_null.call(&mut store, (0,)).unwrap(), 0, "0 is null");
    assert_eq!(non_null.call(&mut store, (7,)).unwrap(), 1, "non-zero is not null");
}
