// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Round-trip soundness corpus — Phase 1 deliverable 2 (#130).
//
// Property: for every well-formed module the producer builds,
//     verify(emit(module)) == OK
// (full structural validation + verify_from_module + verify_access_sites).
// Enforced ECHIDNA-style over a deterministically-generated corpus, plus
// negative controls that MUST be rejected so the property has teeth.
//
// The corpus is generated at the IR level — the producer has no in-process
// `.twasm` parser yet (#127). A `verify(codegen(parse(src)))` corpus over
// real `.twasm` sources follows once the front-end → IR seam lands.

use typed_wasm_codegen::{
    emit, example01, paint_type_tile, paint_type_layer, parser, Field, Func, Memory, Module,
    Op, Ownership, Region, Scalar, Wty,
};
use typed_wasm_verify::{
    verify_access_sites_from_module, verify_from_module, OwnershipError, VerifyError,
};

/// Tiny deterministic PRNG (LCG) — keeps the corpus reproducible with no
/// external dev-dependency.
struct Rng(u64);

impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) as u32
    }
    fn upto(&mut self, n: u32) -> u32 {
        self.next_u32() % n
    }
}

const SCALARS: [Scalar; 8] = [
    Scalar::I32,
    Scalar::U32,
    Scalar::F32,
    Scalar::F64,
    Scalar::I64,
    Scalar::U8,
    Scalar::Bool,
    Scalar::I16,
];

/// Scalar type names as they appear in `.twasm` source text.
const SCALAR_NAMES: [&str; 11] = [
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "bool",
];

/// Generate syntactically-valid `.twasm` SOURCE TEXT within the v0-supported
/// subset: random regions of random scalar fields (some arrays, optional
/// `align`), plus simple named-param functions. Exercises the parser on
/// arbitrary schemas, not just the six hand-written examples.
fn gen_twasm_source(seed: u64) -> String {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(7));
    let mut s = String::new();
    let n_regions = 1 + rng.upto(3);
    for r in 0..n_regions {
        s.push_str(&format!("region R{r} {{\n"));
        let n_fields = 1 + rng.upto(6);
        for fi in 0..n_fields {
            let ty = SCALAR_NAMES[rng.upto(SCALAR_NAMES.len() as u32) as usize];
            if rng.upto(4) == 0 {
                s.push_str(&format!("    f{fi}: {ty}[{}];\n", 1 + rng.upto(16)));
            } else {
                s.push_str(&format!("    f{fi}: {ty};\n"));
            }
        }
        if rng.upto(2) == 0 {
            let aligns = [1u32, 2, 4, 8, 16];
            s.push_str(&format!("    align {};\n", aligns[rng.upto(5) as usize]));
        }
        s.push_str("}\n\n");
    }
    for k in 0..rng.upto(4) {
        let n_params = rng.upto(4);
        let params: Vec<String> = (0..n_params)
            .map(|pi| {
                let ty = SCALAR_NAMES[rng.upto(SCALAR_NAMES.len() as u32) as usize];
                format!("p{pi}: {ty}")
            })
            .collect();
        let ret = if rng.upto(2) == 0 {
            format!(
                " -> {}",
                SCALAR_NAMES[rng.upto(SCALAR_NAMES.len() as u32) as usize]
            )
        } else {
            String::new()
        };
        s.push_str(&format!("fn fn{k}({}){} {{\n}}\n\n", params.join(", "), ret));
    }
    s
}

/// Generate a well-formed module: random scalar regions + functions
/// that use LocalGet/Drop to maintain stack balance.
fn gen_valid(seed: u64) -> Module {
    let mut rng = Rng(seed.wrapping_mul(2654435761).wrapping_add(1));

    let n_regions = 1 + rng.upto(2) as usize;
    let mut regions = Vec::new();
    for r in 0..n_regions {
        let n_fields = 2 + rng.upto(5) as usize;
        let fields = (0..n_fields)
            .map(|i| Field::scalar(&format!("f{r}_{i}"), SCALARS[rng.upto(8) as usize]))
            .collect();
        regions.push(Region {
            name: format!("R{r}"),
            fields,
            byte_size: n_fields as u32 * 4,
        });
    }

    let n_funcs = 1 + rng.upto(4) as usize;
    let mut funcs = Vec::new();
    for k in 0..n_funcs {
        let n_params = 1 + rng.upto(3) as usize;
        let params: Vec<Wty> = (0..n_params).map(|_| Wty::I32).collect();
        let results = if rng.upto(2) == 0 { vec![Wty::I32] } else { vec![] };

        let mut body = Vec::new();
        for i in 0..n_params as u32 {
            body.push(Op::LocalGet(i));
            body.push(Op::Drop);
        }
        if !results.is_empty() {
            body.push(Op::I32Const(0));
        }

        funcs.push(Func {
            name: format!("func{k}"),
            params,
            results,
            body,
            accesses: vec![],
            export: true,
        });
    }

    Module {
        regions,
        memory: Some(Memory {
            min_pages: 4,
            max_pages: Some(64),
        }),
        imports: vec![],
        funcs,
        ownership: vec![],
    }
}

/// The soundness property: emitted bytes validate AND pass both verifier passes.
fn assert_round_trips(m: &Module) {
    let bytes = emit(m);
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .expect("emitted module must be valid wasm");
    verify_from_module(&bytes).expect("emitted module must pass L7/L10 ownership");
    let violations =
        verify_access_sites_from_module(&bytes).expect("access-sites section must parse");
    assert!(
        violations.is_empty(),
        "L2 access-site violations: {violations:?}"
    );
}

#[test]
fn wired_examples_round_trip() {
    assert_round_trips(&example01());
    assert_round_trips(&paint_type_tile());
    assert_round_trips(&paint_type_layer());
}

/// Test that parsing .twasm files and emitting them produces verifiable modules.
/// This closes the front-end -> IR -> codegen seam for paint-type schemas.
///
/// The schemas are vendored under `tests/fixtures/paint-type/` so this test is
/// self-contained in CI (no sibling paint-type checkout required). They mirror
/// `JoshuaJewell/paint-type:src/bridges/paint-type-{tile,layer}.twasm`; refresh
/// the fixtures if the upstream bridge contract changes.
#[test]
fn parsed_paint_type_schemas_round_trip() {
    // Parse and emit paint-type-tile.twasm (vendored fixture)
    let tile_src = include_str!("fixtures/paint-type/paint-type-tile.twasm");
    let tile_module = parser::parse_module(tile_src).expect("paint-type-tile.twasm must parse");
    assert_round_trips(&tile_module);

    // Parse and emit paint-type-layer.twasm (vendored fixture)
    let layer_src = include_str!("fixtures/paint-type/paint-type-layer.twasm");
    let layer_module = parser::parse_module(layer_src).expect("paint-type-layer.twasm must parse");
    assert_round_trips(&layer_module);
    
    // Parse and emit example-01
    let ex01_src = include_str!("../../../examples/01-single-module.twasm");
    let ex01_module = parser::parse_module(ex01_src).expect("01-single-module.twasm must parse");
    assert_round_trips(&ex01_module);
}

/// Round-trip the full example corpus: every `examples/NN-*.twasm` must parse,
/// emit valid wasm, and pass the verifier. This is the v1.0 end-to-end
/// soundness gate (#130) over the canonical six real `.twasm` sources — not
/// just paint-type / example-01. Extending the front-end (ptr<T> fields,
/// unnamed/borrow fn params, annotation clauses, import-region, invariant
/// blocks) took this corpus from 2/6 to 6/6.
#[test]
fn parsed_example_corpus_round_trips() {
    let corpus: [(&str, &str); 6] = [
        ("01-single-module", include_str!("../../../examples/01-single-module.twasm")),
        ("02-multi-module", include_str!("../../../examples/02-multi-module.twasm")),
        ("03-ownership-linearity", include_str!("../../../examples/03-ownership-linearity.twasm")),
        ("04-ecs-game", include_str!("../../../examples/04-ecs-game.twasm")),
        ("05-tropical-cost", include_str!("../../../examples/05-tropical-cost.twasm")),
        ("06-epistemic-sync", include_str!("../../../examples/06-epistemic-sync.twasm")),
    ];
    for (name, src) in corpus {
        let module =
            parser::parse_module(src).unwrap_or_else(|e| panic!("{name}.twasm must parse: {e}"));
        assert_round_trips(&module);
    }
}

/// Reinforce: a malformed or truncated `.twasm` must yield `Ok`/`Err`, never a
/// panic. Feeds char-boundary truncations of every example plus adversarial
/// fragments (unbalanced delimiters, UTF-8, partial type forms) through the
/// parser; the test fails if any input panics (out-of-bounds slice, etc.).
#[test]
fn parser_never_panics_on_malformed_input() {
    let examples: [&str; 6] = [
        include_str!("../../../examples/01-single-module.twasm"),
        include_str!("../../../examples/02-multi-module.twasm"),
        include_str!("../../../examples/03-ownership-linearity.twasm"),
        include_str!("../../../examples/04-ecs-game.twasm"),
        include_str!("../../../examples/05-tropical-cost.twasm"),
        include_str!("../../../examples/06-epistemic-sync.twasm"),
    ];
    for src in examples {
        for cut in (0..src.len()).step_by(7) {
            if src.is_char_boundary(cut) {
                let _ = parser::parse_module(&src[..cut]); // must not panic
            }
        }
    }
    for frag in [
        "", "region", "region X", "region X {", "region X { f: ",
        "region X { f: i32", "fn", "fn f(", "fn f(&mut region<",
        "fn f() -> ", "import region", "import region X from \"",
        "opt<ptr<", "区域 region", "{{{{{", "<<<<<", "region X { invariant {",
    ] {
        let _ = parser::parse_module(frag); // must not panic
    }
}

/// Broaden: arbitrary generated `.twasm` SOURCE (not just the six examples)
/// must parse, emit valid wasm, and round-trip through the verifier — surfaces
/// front-end gaps on schema combinations the hand-written corpus misses.
#[test]
fn generated_twasm_source_round_trips() {
    for seed in 0..256u64 {
        let src = gen_twasm_source(seed);
        match parser::parse_module(&src) {
            Ok(m) => assert_round_trips(&m),
            Err(e) => panic!(
                "generated .twasm failed to parse (seed {seed}): {e}\n--- source ---\n{src}"
            ),
        }
    }
}

#[test]
fn generated_corpus_round_trips() {
    for seed in 0..512u64 {
        assert_round_trips(&gen_valid(seed));
    }
}

/// Climb Step 1: a simple field reader (`region.get $p .field -> x; return x;`)
/// must lower to a REAL typed load, not a representative stub. example03's
/// `read_particle_pos` reads `pos_x: f32` (offset 0) → `[local.get 0,
/// f32.load]` + one access-site, and the module still round-trips.
#[test]
fn reader_body_is_lowered_to_real_load() {
    let src = include_str!("../../../examples/03-ownership-linearity.twasm");
    let m = parser::parse_module(src).expect("03-ownership-linearity.twasm must parse");
    let f = m
        .funcs
        .iter()
        .find(|f| f.name == "read_particle_pos")
        .expect("read_particle_pos present");
    assert!(
        matches!(f.body.as_slice(), [Op::LocalGet(0), Op::F32Load { .. }]),
        "expected real f32.load reader body, got {:?}",
        f.body
    );
    assert_eq!(f.accesses.len(), 1, "reader must record one access-site");
    assert_round_trips(&m);
}

/// Climb Step 2: a single-statement field writer (`region.set $p .field, v;`)
/// must lower to a REAL typed store, not a representative stub — covering a
/// matching-typed param value, a bool/int literal, and the i64/f64 widths added
/// to the `Op` set. A wide field reader (`-> i64`) must now lower to `i64.load`
/// rather than falling back to the stub. The fixture is a self-contained
/// `.twasm` source: no clean single-statement writer exists in the example
/// corpus (their setters sit inside `if`/`while`/arithmetic, which correctly
/// stay on the stub path).
#[test]
fn writer_and_wide_reader_bodies_are_lowered_to_real_memory_ops() {
    // pos_x: f32 @0 (f0), vel_x: f32 @4 (f1), lifetime: i64 @8 (f2),
    // is_alive: bool @16 (f3).
    let src = r#"
        region Particle {
            pos_x: f32;
            vel_x: f32;
            lifetime: i64;
            is_alive: bool;
        }
        memory mem { initial: 1; }

        fn set_vel(p: &mut region<Particle>, v: f32) {
            region.set $p .vel_x, v;
        }
        fn set_life(p: &mut region<Particle>, t: i64) {
            region.set $p .lifetime, t;
        }
        fn reset_life(p: &mut region<Particle>) {
            region.set $p .lifetime, 0;
        }
        fn kill(p: &mut region<Particle>) {
            region.set $p .is_alive, false;
        }
        fn read_life(p: &region<Particle>) -> i64 {
            region.get $p .lifetime -> x;
            return x;
        }
    "#;
    let m = parser::parse_module(src).expect("writer fixture must parse");
    let by = |name: &str| {
        m.funcs
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("{name} present"))
    };

    // param value -> [local.get p, local.get v, f32.store]
    let set_vel = by("set_vel");
    assert!(
        matches!(
            set_vel.body.as_slice(),
            [Op::LocalGet(0), Op::LocalGet(1), Op::F32Store { .. }]
        ),
        "expected real f32.store writer, got {:?}",
        set_vel.body
    );
    assert_eq!(set_vel.accesses.len(), 1, "writer must record one access-site");

    // i64 param value -> [local.get p, local.get t, i64.store]
    assert!(
        matches!(
            by("set_life").body.as_slice(),
            [Op::LocalGet(0), Op::LocalGet(1), Op::I64Store { .. }]
        ),
        "expected i64.store writer, got {:?}",
        by("set_life").body
    );

    // int literal -> [local.get p, i64.const 0, i64.store]
    assert!(
        matches!(
            by("reset_life").body.as_slice(),
            [Op::LocalGet(0), Op::I64Const(0), Op::I64Store { .. }]
        ),
        "expected i64.const literal writer, got {:?}",
        by("reset_life").body
    );

    // bool literal -> [local.get p, i32.const 0, i32.store8] — a 1-byte field
    // uses a 1-byte store, NOT a 4-byte i32.store that would over-run the region.
    assert!(
        matches!(
            by("kill").body.as_slice(),
            [Op::LocalGet(0), Op::I32Const(0), Op::I32Store8 { .. }]
        ),
        "expected bool-literal i32.store8 writer, got {:?}",
        by("kill").body
    );

    // wide reader -> [local.get p, i64.load]
    assert!(
        matches!(
            by("read_life").body.as_slice(),
            [Op::LocalGet(0), Op::I64Load { .. }]
        ),
        "expected i64.load reader, got {:?}",
        by("read_life").body
    );

    assert_round_trips(&m);
}

/// A `region.set` whose value is a compound expression (not a lone param or
/// literal) must NOT be mistaken for a writer — it falls back to the stub, so
/// the module still round-trips and contains no spurious store.
#[test]
fn compound_set_value_falls_back_to_stub() {
    let src = r#"
        region Particle {
            pos_x: f32;
            vel_x: f32;
        }
        memory mem { initial: 1; }
        fn step(p: &mut region<Particle>, dt: f32) {
            region.set $p .pos_x, pos_x + vel_x * dt;
        }
    "#;
    let m = parser::parse_module(src).expect("compound-set fixture must parse");
    let step = m
        .funcs
        .iter()
        .find(|f| f.name == "step")
        .expect("step present");
    assert!(
        !step
            .body
            .iter()
            .any(|op| matches!(op, Op::F32Store { .. } | Op::I32Store { .. })),
        "compound expression must not lower to a store, got {:?}",
        step.body
    );
    assert_round_trips(&m);
}

/// Narrow scalar fields (1/2-byte) must lower to sub-width ops so a write
/// touches ONLY its own bytes — never the adjacent packed field, never past the
/// region. A full-width i32.store/i32.load would corrupt/over-read the neighbour
/// (validates clean, so the verifier can't catch it — caught here instead).
#[test]
fn narrow_fields_use_subwidth_ops_and_do_not_clobber_neighbours() {
    // flags: bool @0 (1 byte, f0), hp: i32 @1 (f1). A naive i32.store of flags
    // at offset 0 would write bytes 0..4, clobbering 3 bytes of hp at 1..5.
    let src = r#"
        region E {
            flags: bool;
            hp: i32;
            small: u16;
            tiny: i8;
        }
        memory mem { initial: 1; }
        fn set_flags(p: &mut region<E>, v: u32) { region.set $p .flags, v; }
        fn set_small(p: &mut region<E>, v: u32) { region.set $p .small, v; }
        fn get_flags(p: &region<E>) -> i32 { region.get $p .flags -> x; return x; }
        fn get_tiny(p: &region<E>) -> i32 { region.get $p .tiny -> x; return x; }
        fn get_small(p: &region<E>) -> i32 { region.get $p .small -> x; return x; }
    "#;
    let m = parser::parse_module(src).expect("narrow-field fixture must parse");
    let by = |name: &str| {
        m.funcs
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("{name} present"))
    };

    // 1-byte store -> store8 (not store) so hp at offset 1 is untouched.
    assert!(
        matches!(
            by("set_flags").body.as_slice(),
            [Op::LocalGet(0), Op::LocalGet(1), Op::I32Store8 { .. }]
        ),
        "bool field must store8, got {:?}",
        by("set_flags").body
    );
    // 2-byte store -> store16.
    assert!(
        matches!(
            by("set_small").body.as_slice(),
            [Op::LocalGet(0), Op::LocalGet(1), Op::I32Store16 { .. }]
        ),
        "u16 field must store16, got {:?}",
        by("set_small").body
    );
    // unsigned narrow load -> zero-extend; signed narrow load -> sign-extend.
    assert!(
        matches!(by("get_flags").body.as_slice(), [Op::LocalGet(0), Op::I32Load8U { .. }]),
        "bool field must load8_u, got {:?}",
        by("get_flags").body
    );
    assert!(
        matches!(by("get_tiny").body.as_slice(), [Op::LocalGet(0), Op::I32Load8S { .. }]),
        "i8 field must load8_s, got {:?}",
        by("get_tiny").body
    );
    assert!(
        matches!(by("get_small").body.as_slice(), [Op::LocalGet(0), Op::I32Load16U { .. }]),
        "u16 field must load16_u, got {:?}",
        by("get_small").body
    );
    assert_round_trips(&m);
}

/// A region-handle parameter must NOT be accepted as the stored scalar value
/// (both are i32 on the wasm stack, but storing a pointer into a scalar field is
/// type confusion). It falls back to the stub instead of emitting a store.
#[test]
fn region_handle_is_not_laundered_into_a_scalar_field() {
    let src = r#"
        region R { flag: i32; }
        memory mem { initial: 1; }
        fn copy_handle(p: &mut region<R>, q: &region<R>) { region.set $p .flag, q; }
    "#;
    let m = parser::parse_module(src).expect("handle-as-value fixture must parse");
    let f = m.funcs.iter().find(|f| f.name == "copy_handle").expect("present");
    assert!(
        !f.body.iter().any(|op| matches!(op, Op::I32Store { .. })),
        "a region handle must not be stored as a scalar value, got {:?}",
        f.body
    );
    assert_round_trips(&m);
}

/// An integer literal outside the field's wasm width must NOT silently wrap
/// (`4294967296 as i32 == 0`); it falls back to the stub. In-range bit patterns
/// (incl. 0xFFFFFFFF -> -1) still lower.
#[test]
fn out_of_range_int_literal_falls_back_to_stub() {
    let src = r#"
        region R { x: i32; }
        memory mem { initial: 1; }
        fn over(p: &mut region<R>) { region.set $p .x, 4294967296; }
        fn inrange(p: &mut region<R>) { region.set $p .x, 0xFFFFFFFF; }
    "#;
    let m = parser::parse_module(src).expect("literal-range fixture must parse");
    let by = |name: &str| m.funcs.iter().find(|f| f.name == name).unwrap();
    assert!(
        !by("over").body.iter().any(|op| matches!(op, Op::I32Store { .. })),
        "2^32 must not wrap to a stored i32.const, got {:?}",
        by("over").body
    );
    // 0xFFFFFFFF fits u32 -> stored as i32.const(-1).
    assert!(
        matches!(
            by("inrange").body.as_slice(),
            [Op::LocalGet(0), Op::I32Const(-1), Op::I32Store { .. }]
        ),
        "0xFFFFFFFF must store as i32.const(-1), got {:?}",
        by("inrange").body
    );
    assert_round_trips(&m);
}

/// A finite float literal whose magnitude overflows f32 to ±inf must NOT be
/// stored as `f32.const inf` (silent value change); it falls back to the stub.
#[test]
fn f32_overflow_literal_falls_back_to_stub() {
    // ~4e38 > f32::MAX (~3.4e38), written without an exponent per the grammar.
    let src = r#"
        region R { x: f32; }
        memory mem { initial: 1; }
        fn huge(p: &mut region<R>) { region.set $p .x, 400000000000000000000000000000000000000.0; }
        fn ok(p: &mut region<R>) { region.set $p .x, 1.5; }
    "#;
    let m = parser::parse_module(src).expect("f32-overflow fixture must parse");
    let by = |name: &str| m.funcs.iter().find(|f| f.name == name).unwrap();
    assert!(
        !by("huge").body.iter().any(|op| matches!(op, Op::F32Store { .. })),
        "overflowing float must not store as f32.const inf, got {:?}",
        by("huge").body
    );
    assert!(
        matches!(
            by("ok").body.as_slice(),
            [Op::LocalGet(0), Op::F32Const(_), Op::F32Store { .. }]
        ),
        "in-range float must lower, got {:?}",
        by("ok").body
    );
    assert_round_trips(&m);
}

/// A synthesised memory (module declares none) must be large enough to cover the
/// accessed region, so a real store/load offset can't point past linear memory
/// and trap at runtime.
#[test]
fn synthesised_memory_covers_a_large_region() {
    // pad: u8[100000] pushes x to byte offset 100000 (> one 64 KiB page).
    let src = r#"
        region Big { pad: u8[100000]; x: i32; }
        fn set_x(p: &mut region<Big>, v: i32) { region.set $p .x, v; }
    "#;
    let m = parser::parse_module(src).expect("large-region fixture must parse");
    let mem = m.memory.expect("a memory must be synthesised for the store");
    // x is at offset 100000; the store reaches bytes 100000..100004, so memory
    // must span at least that many bytes (>= 2 pages).
    assert!(
        mem.min_pages * 65536 >= 100004,
        "synthesised memory ({} pages) must cover offset 100000, ",
        mem.min_pages
    );
    assert_round_trips(&m);
}

fn one_func_module(kind: Ownership, body: Vec<Op>) -> Module {
    Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "subject".into(),
            params: vec![Wty::I32],
            results: vec![],
            body,
            accesses: vec![],
            export: true,
        }],
        ownership: vec![(0, vec![kind])],
    }
}

fn expect_ownership_reject(m: &Module, pred: impl Fn(&OwnershipError) -> bool, what: &str) {
    let bytes = emit(m);
    match verify_from_module(&bytes) {
        Err(VerifyError::Ownership(errs)) => {
            assert!(errs.iter().any(pred), "expected {what}, got {errs:?}")
        }
        other => panic!("expected {what} to be rejected, got {other:?}"),
    }
}

#[test]
fn malformed_modules_are_rejected() {
    expect_ownership_reject(
        &one_func_module(
            Ownership::Linear,
            vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop],
        ),
        |e| matches!(e, OwnershipError::LinearUsedMultiple { .. }),
        "LinearUsedMultiple",
    );
    expect_ownership_reject(
        &one_func_module(
            Ownership::ExclBorrow,
            vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop],
        ),
        |e| matches!(e, OwnershipError::ExclBorrowAliased { .. }),
        "ExclBorrowAliased",
    );
    expect_ownership_reject(
        &one_func_module(Ownership::Linear, vec![]),
        |e| matches!(e, OwnershipError::LinearNotUsed { .. }),
        "LinearNotUsed",
    );
}
