// SPDX-License-Identifier: MPL-2.0
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
    emit, example01, example03, Access, Body, Field, FieldTy, Func, Memory, Module, Op, Ownership,
    Region, Scalar, Stmt, Wty,
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

/// The wasm value type a scalar leaf loads/stores as.
fn scalar_to_wty(s: Scalar) -> Wty {
    match s {
        Scalar::F32 => Wty::F32,
        Scalar::F64 => Wty::F64,
        Scalar::I64 | Scalar::U64 => Wty::I64,
        _ => Wty::I32, // i8/i16/i32/u8/u16/u32/bool move through i32
    }
}

/// Generate a well-formed module: random scalar regions + getter/setter
/// functions, each reading/writing a real field through a once-read base
/// local (so the ownership annotations stay clean).
fn gen_valid(seed: u64) -> Module {
    let mut rng = Rng(seed.wrapping_mul(2654435761).wrapping_add(1));

    let n_regions = 1 + rng.upto(2) as usize; // 1..=2
    let mut regions = Vec::new();
    for r in 0..n_regions {
        let n_fields = 2 + rng.upto(5) as usize; // 2..=6
        let fields = (0..n_fields)
            .map(|i| Field::scalar(&format!("f{r}_{i}"), SCALARS[rng.upto(8) as usize]))
            .collect();
        regions.push(Region::new(&format!("R{r}"), fields));
    }

    let n_funcs = 1 + rng.upto(4) as usize; // 1..=4
    let mut funcs = Vec::new();
    let mut ownership = Vec::new();
    for k in 0..n_funcs {
        let region = rng.upto(n_regions as u32) as usize;
        let field = rng.upto(regions[region].fields.len() as u32) as usize;
        let scalar = match regions[region].fields[field].ty {
            FieldTy::Scalar(s) => s,
            _ => Scalar::I32,
        };
        let wty = scalar_to_wty(scalar);
        let idx = if rng.upto(2) == 0 { Some(1u32) } else { None };

        if rng.upto(2) == 0 {
            funcs.push(Func {
                name: format!("get{k}"),
                params: vec![Wty::I32, Wty::I32],
                results: vec![wty],
                body: Body::Typed {
                    handles: vec![0],
                    stmts: vec![Stmt::Return(Access::field(0, idx, region, field))],
                },
                export: true,
            });
            ownership.push((k, vec![Ownership::SharedBorrow, Ownership::Unrestricted]));
        } else {
            funcs.push(Func {
                name: format!("set{k}"),
                params: vec![Wty::I32, Wty::I32, wty],
                results: vec![],
                body: Body::Typed {
                    handles: vec![0],
                    stmts: vec![Stmt::Set {
                        access: Access::field(0, idx, region, field),
                        value: 2,
                    }],
                },
                export: true,
            });
            ownership.push((
                k,
                vec![
                    Ownership::ExclBorrow,
                    Ownership::Unrestricted,
                    Ownership::Unrestricted,
                ],
            ));
        }
    }

    Module {
        regions,
        memory: Some(Memory {
            min_pages: 4,
            max_pages: Some(64),
        }),
        imports: vec![],
        funcs,
        ownership,
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
    assert_round_trips(&example03());
}

#[test]
fn generated_corpus_round_trips() {
    // 512 deterministically-generated modules; every one must satisfy
    // verify(emit(m)) == OK.
    for seed in 0..512u64 {
        assert_round_trips(&gen_valid(seed));
    }
}

// ── Negative controls — the property must have teeth ──────────────────

fn one_func_module(kind: Ownership, body: Vec<Op>) -> Module {
    Module {
        regions: vec![],
        memory: None,
        imports: vec![],
        funcs: vec![Func {
            name: "subject".into(),
            params: vec![Wty::I32],
            results: vec![],
            body: Body::Ops(body),
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
    // Double-free: a Linear (own) handle used twice.
    expect_ownership_reject(
        &one_func_module(
            Ownership::Linear,
            vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop],
        ),
        |e| matches!(e, OwnershipError::LinearUsedMultiple { .. }),
        "LinearUsedMultiple",
    );
    // Aliasing: a &mut (ExclBorrow) handle referenced twice.
    expect_ownership_reject(
        &one_func_module(
            Ownership::ExclBorrow,
            vec![Op::LocalGet(0), Op::LocalGet(0), Op::Drop, Op::Drop],
        ),
        |e| matches!(e, OwnershipError::ExclBorrowAliased { .. }),
        "ExclBorrowAliased",
    );
    // Leak: a Linear (own) handle never consumed.
    expect_ownership_reject(
        &one_func_module(Ownership::Linear, vec![]),
        |e| matches!(e, OwnershipError::LinearNotUsed { .. }),
        "LinearNotUsed",
    );
}
