// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Tier-2 access-TYPING gate for codegen → verifier self-certification.
//
// The round-trip corpus proves the emitted module VALIDATES; the
// execution gate (tests/execute_lowering.rs) proves it COMPUTES the right
// memory semantics. This file proves the third leg: the verifier can,
// from the emitted bytes ALONE (no producer trust), DECODE each pinned
// access site and confirm the instruction there is a load/store of the
// target field's exact type, width, and offset, in-region. This is the
// obligation proposal 0002 deferred as `AccessSiteMisalignment`.
//
//   * positive   — real lowered reader/writer bodies type-verify, no
//                  declared-only residue, no errors;
//   * legibility — hand-written representative IR (example01) is reported
//                  as declared-only, NOT silently passed as type-verified;
//   * teeth      — a pinned site whose instruction is the wrong width,
//                  wrong offset, not a memory op, out of range, or out of
//                  region is REJECTED with the matching error variant. A
//                  pass with no teeth would "verify" a miscompilation.

use typed_wasm_codegen::{emit, emit_example01, parser, Field, Func, Memory, Module, Op, Region, Scalar, Wty};
use typed_wasm_verify::{verify_access_typing_from_module, AccessTypingError};

// ---- positive: real lowering type-verifies -------------------------------

const MIXED: &str = r#"
    region R {
        a: i32;
        b: u8;
        c: f64;
    }
    memory mem { initial: 1; }

    fn get_a(p: &region<R>) -> i32 { region.get $p .a -> x; return x; }
    fn set_b(p: &mut region<R>, v: u32) { region.set $p .b, v; }
    fn get_c(p: &region<R>) -> f64 { region.get $p .c -> x; return x; }
"#;

#[test]
fn real_lowered_pinned_sites_type_verify() {
    let module = parser::parse_module(MIXED).expect("fixture must parse");
    let bytes = emit(&module);

    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");

    // a (i32.load @0), b (i32.store8 @4), c (f64.load @5) — all pinned by
    // the parser's real lowering, all checked against the field schema.
    assert_eq!(report.type_verified, 3, "every real-lowered site is checked");
    assert_eq!(report.declared_only, 0, "real lowering pins, never declares-only");
    assert!(
        report.errors.is_empty(),
        "correct lowering must type-check cleanly, got {:?}",
        report.errors
    );
}

// ---- legibility: representative IR is declared-only, not laundered --------

#[test]
fn representative_ir_is_reported_declared_only() {
    // example01() is hand-written IR whose bodies are illustrative stubs
    // (e.g. move_player stores an f32 into a u8[] field). Tier 2 must NOT
    // claim those as type-verified — they are honestly declared-only.
    let bytes = emit_example01();
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");

    assert_eq!(report.type_verified, 0, "no representative site is pinned");
    assert_eq!(
        report.declared_only, 6,
        "example01 carries 6 declared-only access sites"
    );
    assert!(
        report.errors.is_empty(),
        "declared-only sites are not errors, got {:?}",
        report.errors
    );
}

// ---- teeth: each fault class is caught -----------------------------------

/// Build a single-region, single-function module with a declared memory.
fn rig(region: Region, func: Func) -> Module {
    Module {
        regions: vec![region],
        memory: Some(Memory {
            min_pages: 1,
            max_pages: None,
        }),
        imports: vec![],
        funcs: vec![func],
        ownership: vec![],
        region_imports: vec![],
    }
}

fn region_ab() -> Region {
    // a: i32 @0, b: u8 @4  (byte_size 5)
    Region {
        name: "R".into(),
        fields: vec![Field::scalar("a", Scalar::I32), Field::scalar("b", Scalar::U8)],
        byte_size: 5,
    }
}

/// A hand-pinned access site (the producer field is private, so go via the
/// public `accesses` vec on `Func`).
fn pinned(region: usize, field: usize, k: usize) -> typed_wasm_codegen::AccessSite {
    typed_wasm_codegen::AccessSite {
        region,
        field,
        instr_index: Some(k),
    }
}

#[test]
fn teeth_wrong_width_is_type_mismatch() {
    // Field b is u8 (@4), but the body loads it with i32.load — a 4-byte
    // read of a 1-byte field. Valid wasm; a typing fault.
    let func = Func {
        name: "bad".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I32],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 4 }],
        accesses: vec![pinned(0, 1, 1)], // field 1 = b (u8)
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert_eq!(report.type_verified, 0);
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessTypeMismatch { field_id: 1, .. }]
        ),
        "expected AccessTypeMismatch on field 1, got {:?}",
        report.errors
    );
}

#[test]
fn teeth_wrong_offset_is_offset_mismatch() {
    // Field a is i32 @0, the op is the right kind (i32.load) but at the
    // wrong static offset.
    let func = Func {
        name: "bad".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I32],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 99 }],
        accesses: vec![pinned(0, 0, 1)], // field 0 = a (i32 @0)
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessOffsetMismatch {
                expected_offset: 0,
                found_offset: 99,
                ..
            }]
        ),
        "expected AccessOffsetMismatch 0 vs 99, got {:?}",
        report.errors
    );
}

#[test]
fn teeth_non_memory_op_is_rejected() {
    // The pinned index points at a non-memory instruction (Drop).
    let func = Func {
        name: "bad".into(),
        params: vec![Wty::I32],
        results: vec![],
        body: vec![Op::LocalGet(0), Op::Drop],
        accesses: vec![pinned(0, 0, 1)], // index 1 = Drop
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessSiteNotAMemoryOp { .. }]
        ),
        "expected AccessSiteNotAMemoryOp, got {:?}",
        report.errors
    );
}

#[test]
fn teeth_index_past_end_is_out_of_range() {
    let func = Func {
        name: "bad".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I32],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
        accesses: vec![pinned(0, 0, 9)], // body has 3 ops incl End
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessSiteIndexOutOfRange {
                instruction_index: 9,
                ..
            }]
        ),
        "expected AccessSiteIndexOutOfRange 9, got {:?}",
        report.errors
    );
}

#[test]
fn teeth_field_past_region_size_is_out_of_region() {
    // Region claims byte_size 4, but field a is i64 (8 bytes @0): the
    // field extent [0,8) exceeds the declared region size.
    let region = Region {
        name: "R".into(),
        fields: vec![Field::scalar("a", Scalar::I64)],
        byte_size: 4, // too small for an i64 field
    };
    let func = Func {
        name: "bad".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I64],
        body: vec![Op::LocalGet(0), Op::I64Load { offset: 0 }],
        accesses: vec![pinned(0, 0, 1)],
        export: true,
    };
    let bytes = emit(&rig(region, func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessOutOfRegionBounds {
                field_offset: 0,
                field_width: 8,
                region_byte_size: 4,
                ..
            }]
        ),
        "expected AccessOutOfRegionBounds, got {:?}",
        report.errors
    );
}

#[test]
fn teeth_correct_handbuilt_site_type_verifies() {
    // The control: the SAME rig with a correct body + pin must pass, so
    // the teeth above are rejecting the fault, not the harness.
    let func = Func {
        name: "good".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I32],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
        accesses: vec![pinned(0, 0, 1)], // field 0 = a (i32 @0)
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert_eq!(report.type_verified, 1);
    assert!(report.errors.is_empty(), "got {:?}", report.errors);
}
