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
use typed_wasm_verify::section::{parse_access_sites_section_payload, AccessSiteEntry};
use typed_wasm_verify::{
    verify_access_typing_from_module, AccessTypingError, ACCESS_SITES_SECTION_NAME,
};

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
        locals: vec![],
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
        locals: vec![],
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
        locals: vec![],
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
        locals: vec![],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
        accesses: vec![pinned(0, 0, 9)], // body has 3 ops incl End
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    // Body bytes: locals vec (1) + local.get 0 (2) + i32.load (3) + end
    // (1) = 7. IR index 9 overshoots the 3 operators by 6, so the emitter
    // writes offset 7 + 6 = 13, which the verifier reports as past the end.
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessSiteOffsetOutOfRange {
                byte_offset: 13,
                body_len: 7,
                ..
            }]
        ),
        "expected AccessSiteOffsetOutOfRange 13 >= 7, got {:?}",
        report.errors
    );
}

#[test]
fn teeth_huge_index_never_collides_with_unpinned_sentinel() {
    // body_len (7) + an overshoot near u32::MAX saturates. A saturated
    // offset of u32::MAX would be the ACCESS_SITE_UNPINNED sentinel, so a
    // producer bug would be counted as a declared-only site instead of
    // being reported. The emitter must clamp below the sentinel.
    let func = Func {
        name: "bad".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I32],
        locals: vec![],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
        accesses: vec![pinned(0, 0, (u32::MAX - 1) as usize)],
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert_eq!(
        report.declared_only, 0,
        "an invalid pinned index must not be laundered into a declared-only site"
    );
    assert!(
        matches!(
            report.errors.as_slice(),
            [AccessTypingError::AccessSiteOffsetOutOfRange { body_len: 7, .. }]
        ),
        "expected AccessSiteOffsetOutOfRange, got {:?}",
        report.errors
    );
}

// ---- ADR-0003: the wire carries BYTE OFFSETS, not operator indices -------

/// Pull the decoded `typedwasm.access-sites` entries out of emitted bytes.
fn access_entries(bytes: &[u8]) -> Vec<AccessSiteEntry> {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CustomSection(r) = payload.expect("valid wasm") {
            if r.name() == ACCESS_SITES_SECTION_NAME {
                return parse_access_sites_section_payload(r.data())
                    .expect("access-sites carrier must decode");
            }
        }
    }
    panic!("no access-sites section emitted");
}

#[test]
fn emitted_offset_is_the_adr_0003_byte_offset() {
    // One declared i32 local, so the locals vector is 3 bytes
    // (count=1, n=1, type=i32). Then local.get 0 is 2 bytes, so the
    // i32.load (IR index 1) starts at byte 5 of the body. An emitter that
    // wrote the operator index would put 1 on the wire.
    let func = Func {
        name: "good".into(),
        params: vec![Wty::I32],
        results: vec![Wty::I32],
        locals: vec![Wty::I32],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
        accesses: vec![pinned(0, 0, 1)],
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let entries = access_entries(&bytes);
    assert_eq!(entries.len(), 1);
    assert_eq!(
        entries[0].instruction_byte_offset, 5,
        "byte offset, not index 1"
    );

    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert_eq!(report.type_verified, 1);
    assert!(report.errors.is_empty(), "got {:?}", report.errors);
}

#[test]
fn every_real_lowered_offset_lands_on_its_instruction() {
    // For the parser's real lowering, decode each body independently and
    // check that every pinned wire offset is the start of a load/store.
    // This pins the producer convention to the bytes, not to the verifier.
    let module = parser::parse_module(MIXED).expect("fixture must parse");
    let bytes = emit(&module);
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("valid wasm") {
            bodies.push(body);
        }
    }
    let entries = access_entries(&bytes);
    assert_eq!(entries.len(), 3);
    for e in &entries {
        let body = &bodies[e.func_idx as usize];
        let start = body.range().start;
        let mut hit = false;
        for item in body
            .get_operators_reader()
            .unwrap()
            .into_iter_with_offsets()
        {
            let (op, pos) = item.unwrap();
            if pos - start == e.instruction_byte_offset as usize {
                let name = format!("{op:?}");
                assert!(
                    name.contains("Load") || name.contains("Store"),
                    "offset {} lands on {name}",
                    e.instruction_byte_offset
                );
                hit = true;
            }
        }
        assert!(
            hit,
            "offset {} is not an instruction boundary",
            e.instruction_byte_offset
        );
    }
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
        locals: vec![],
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
        locals: vec![],
        body: vec![Op::LocalGet(0), Op::I32Load { offset: 0 }],
        accesses: vec![pinned(0, 0, 1)], // field 0 = a (i32 @0)
        export: true,
    };
    let bytes = emit(&rig(region_ab(), func));
    let report = verify_access_typing_from_module(&bytes).expect("typing pass runs");
    assert_eq!(report.type_verified, 1);
    assert!(report.errors.is_empty(), "got {:?}", report.errors);
}
