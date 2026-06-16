// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Tier-1 differential EXECUTION gate for codegen body lowering (climb Step 1/2).
//
// The round-trip corpus proves the emitted module VALIDATES; this proves it
// COMPUTES the intended memory semantics. We instantiate the lowered module in
// an in-process wasm engine (wasmi — pure Rust, so it runs in CI without a
// system wasmtime, unlike tests/execute.rs) and exercise the real store/load
// bodies the parser lowers:
//
//   * value round-trip — set(field, v) then get(field) == v, for every scalar
//     width, including narrow u8/u16 zero-extension and i8 sign-extension;
//   * no clobber — a narrow store touches ONLY its own bytes, so re-writing a
//     narrow field leaves the following packed fields intact.
//
// A wrong width / offset / extension — exactly the class the L2/L7/L10 verifier
// is blind to (it never decodes the code section's memargs) — fails HERE. This
// is what turns "the op widths argue correctness" into "the engine demonstrates
// it".

use typed_wasm_codegen::{emit, parser};
use wasmi::{Engine, Linker, Module, Store, TypedFunc};

// Packed mixed-width region. The narrow fields (flag/small/sign) are sandwiched
// between wider neighbours so an over-wide store would be observable.
//   head:i32 @0 | flag:u8 @4 | small:u16 @5 | sign:i8 @7 | big:i64 @8
//   | fx:f32 @16 | fy:f64 @20   (byte_size = 28)
const SRC: &str = r#"
    region Mix {
        head: i32;
        flag: u8;
        small: u16;
        sign: i8;
        big: i64;
        fx: f32;
        fy: f64;
    }
    memory mem { initial: 1; }

    fn set_head(p: &mut region<Mix>, v: i32) { region.set $p .head, v; }
    fn get_head(p: &region<Mix>) -> i32 { region.get $p .head -> x; return x; }
    fn set_flag(p: &mut region<Mix>, v: u32) { region.set $p .flag, v; }
    fn get_flag(p: &region<Mix>) -> i32 { region.get $p .flag -> x; return x; }
    fn set_small(p: &mut region<Mix>, v: u32) { region.set $p .small, v; }
    fn get_small(p: &region<Mix>) -> i32 { region.get $p .small -> x; return x; }
    fn set_sign(p: &mut region<Mix>, v: i32) { region.set $p .sign, v; }
    fn get_sign(p: &region<Mix>) -> i32 { region.get $p .sign -> x; return x; }
    fn set_big(p: &mut region<Mix>, v: i64) { region.set $p .big, v; }
    fn get_big(p: &region<Mix>) -> i64 { region.get $p .big -> x; return x; }
    fn set_fx(p: &mut region<Mix>, v: f32) { region.set $p .fx, v; }
    fn get_fx(p: &region<Mix>) -> f32 { region.get $p .fx -> x; return x; }
    fn set_fy(p: &mut region<Mix>, v: f64) { region.set $p .fy, v; }
    fn get_fy(p: &region<Mix>) -> f64 { region.get $p .fy -> x; return x; }
"#;

#[test]
fn lowered_store_load_bodies_execute_with_correct_semantics() {
    let module_ir = parser::parse_module(SRC).expect("Mix fixture must parse");
    let bytes = emit(&module_ir);

    let engine = Engine::default();
    // wasmi validates on load — a second independent well-formedness oracle.
    let module = Module::new(&engine, &bytes[..]).expect("emitted module loads into wasmi");
    let mut store = Store::new(&engine, ());
    let linker = <Linker<()>>::new(&engine);
    let instance = linker
        .instantiate_and_start(&mut store, &module)
        .expect("instantiate");

    macro_rules! tf {
        ($name:literal, $p:ty, $r:ty) => {{
            let f: TypedFunc<$p, $r> = instance
                .get_typed_func::<$p, $r>(&store, $name)
                .unwrap_or_else(|e| panic!("export {}: {e}", $name));
            f
        }};
    }

    let set_head = tf!("set_head", (i32, i32), ());
    let get_head = tf!("get_head", (i32,), i32);
    let set_flag = tf!("set_flag", (i32, i32), ());
    let get_flag = tf!("get_flag", (i32,), i32);
    let set_small = tf!("set_small", (i32, i32), ());
    let get_small = tf!("get_small", (i32,), i32);
    let set_sign = tf!("set_sign", (i32, i32), ());
    let get_sign = tf!("get_sign", (i32,), i32);
    let set_big = tf!("set_big", (i32, i64), ());
    let get_big = tf!("get_big", (i32,), i64);
    let set_fx = tf!("set_fx", (i32, f32), ());
    let get_fx = tf!("get_fx", (i32,), f32);
    let set_fy = tf!("set_fy", (i32, f64), ());
    let get_fy = tf!("get_fy", (i32,), f64);

    const BASE: i32 = 0;
    let big_sentinel: i64 = 0x0123_4567_89AB_CDEF;

    // ---- Phase A: each field round-trips its own value at its own offset ----
    set_head.call(&mut store, (BASE, 0x1234_5678)).unwrap();
    set_flag.call(&mut store, (BASE, 200)).unwrap();
    set_small.call(&mut store, (BASE, 48879)).unwrap(); // 0xBEEF
    set_sign.call(&mut store, (BASE, -5)).unwrap();
    set_big.call(&mut store, (BASE, big_sentinel)).unwrap();
    set_fx.call(&mut store, (BASE, 1.5)).unwrap();
    set_fy.call(&mut store, (BASE, 2.25)).unwrap();

    assert_eq!(get_head.call(&mut store, (BASE,)).unwrap(), 0x1234_5678);
    assert_eq!(get_flag.call(&mut store, (BASE,)).unwrap(), 200, "u8 zero-extend");
    assert_eq!(get_small.call(&mut store, (BASE,)).unwrap(), 48879, "u16 zero-extend");
    assert_eq!(get_sign.call(&mut store, (BASE,)).unwrap(), -5, "i8 sign-extend");
    assert_eq!(get_big.call(&mut store, (BASE,)).unwrap(), big_sentinel);
    assert_eq!(get_fx.call(&mut store, (BASE,)).unwrap(), 1.5);
    assert_eq!(get_fy.call(&mut store, (BASE,)).unwrap(), 2.25);

    // ---- Phase B: a narrow store touches ONLY its own bytes ----
    // Re-write each narrow field with a fresh value; the FOLLOWING packed fields
    // (set in Phase A, not rewritten here) must be untouched. A full-width store
    // would corrupt them and fail one of these asserts.
    set_flag.call(&mut store, (BASE, 165)).unwrap(); // 0xA5
    assert_eq!(get_flag.call(&mut store, (BASE,)).unwrap(), 165);
    assert_eq!(get_small.call(&mut store, (BASE,)).unwrap(), 48879, "flag store overran into small");
    assert_eq!(get_sign.call(&mut store, (BASE,)).unwrap(), -5, "flag store overran into sign");

    set_small.call(&mut store, (BASE, 4660)).unwrap(); // 0x1234
    assert_eq!(get_small.call(&mut store, (BASE,)).unwrap(), 4660);
    assert_eq!(get_sign.call(&mut store, (BASE,)).unwrap(), -5, "small store overran into sign");
    assert_eq!(get_big.call(&mut store, (BASE,)).unwrap(), big_sentinel, "small store overran into big");

    set_sign.call(&mut store, (BASE, 51)).unwrap(); // 0x33
    assert_eq!(get_sign.call(&mut store, (BASE,)).unwrap(), 51);
    assert_eq!(get_big.call(&mut store, (BASE,)).unwrap(), big_sentinel, "sign store overran into big");

    // The wider neighbours that bracket the narrow block are also still intact.
    assert_eq!(get_head.call(&mut store, (BASE,)).unwrap(), 0x1234_5678, "head corrupted");
    assert_eq!(get_big.call(&mut store, (BASE,)).unwrap(), big_sentinel, "big corrupted");
}
