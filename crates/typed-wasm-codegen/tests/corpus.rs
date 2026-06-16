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
