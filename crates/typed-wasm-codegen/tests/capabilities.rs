// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// L15 resource capabilities at the `.twasm` front-end: L15-A (distinct
// declarations), L15-B (caps are declared) and L15-C (a caller's caps contain
// its callee's), the surface form of `ResourceCapabilities.idr`'s
// `DistinctCaps`, `ContainedIn` and `CallCompatible`. Each rule has a program
// it accepts and one it must refuse.

use typed_wasm_codegen::parser::parse_module;

fn refused(src: &str) -> String {
    match parse_module(src) {
        Ok(_) => panic!("program must be refused:\n{src}"),
        Err(e) => e,
    }
}

const ACCEPTED: &str = r#"
capability net;
capability fs;

fn send(x: i32) -> i32
    effects { memory: { Read }, caps: { net } }
{
    return x;
}

fn sync(x: i32) -> i32
    effects { memory: { Read }, caps: { net, fs } }
{
    let a: i32 = send(x);
    if a > 0 {
        return send(a);
    }
    return a;
}

fn pure_helper(x: i32) -> i32 {
    return x;
}

fn plain(x: i32) -> i32 {
    // send(x) here is only a comment
    return pure_helper(x);
}
"#;

#[test]
fn accepts_well_formed_capabilities_and_calls() {
    parse_module(ACCEPTED).expect("well-formed L15 program must parse");
}

#[test]
fn l15a_refuses_a_duplicate_declaration() {
    let e = refused("capability net;\ncapability net;\nfn f() -> i32 { return 0; }\n");
    assert!(e.contains("L15-A") && e.contains("'net'"), "{e}");
}

#[test]
fn l15b_refuses_an_undeclared_capability() {
    let e = refused(
        "capability net;\n\
         fn f() -> i32 effects { memory: { Read }, caps: { net, fs } } { return 0; }\n",
    );
    assert!(
        e.contains("L15-B") && e.contains("'fs'") && !e.contains("'net'"),
        "{e}"
    );
}

#[test]
fn l15c_refuses_a_caller_missing_a_callee_capability() {
    let e = refused(
        "capability net;\ncapability fs;\n\
         fn write_file() -> i32 effects { caps: { fs } } { return 0; }\n\
         fn upload() -> i32 effects { caps: { net } } { return write_file(); }\n",
    );
    assert!(
        e.contains("L15-C") && e.contains("'upload' calls 'write_file'") && e.contains("{ fs }"),
        "{e}"
    );
}

#[test]
fn l15c_refuses_a_caller_without_caps_calling_a_capped_function() {
    // No caps clause means no capabilities: calling `send` would launder `net`.
    let e = refused(
        "capability net;\n\
         fn send() -> i32 effects { caps: { net } } { return 0; }\n\
         fn quiet() -> i32 { if 1 > 0 { return send(); } return 0; }\n",
    );
    assert!(
        e.contains("L15-C") && e.contains("'quiet' calls 'send'"),
        "{e}"
    );
}

#[test]
fn l15c_checks_calls_to_functions_declared_later() {
    let e = refused(
        "capability net;\n\
         fn early() -> i32 { return late(); }\n\
         fn late() -> i32 effects { caps: { net } } { return 0; }\n",
    );
    assert!(e.contains("'early' calls 'late'"), "{e}");
}

#[test]
fn l15c_is_per_call_site_not_transitive_only() {
    // f -> g -> h. g holds h's `net`, so g -> h is fine; f holds nothing and
    // g requires `net`, so the f -> g edge alone is refused.
    let e = refused(
        "capability net;\n\
         fn h() -> i32 effects { caps: { net } } { return 0; }\n\
         fn g() -> i32 effects { caps: { net } } { return h(); }\n\
         fn f() -> i32 { return g(); }\n",
    );
    assert!(
        e.contains("'f' calls 'g'") && !e.contains("'g' calls 'h'"),
        "{e}"
    );
}

#[test]
fn calls_in_comments_and_strings_do_not_count() {
    parse_module(
        "capability net;\n\
         fn send() -> i32 effects { caps: { net } } { return 0; }\n\
         fn f() -> i32 {\n  // send()\n  /* send() */\n  return 0;\n}\n",
    )
    .expect("a call that only appears in a comment is not a call");
}

#[test]
fn a_non_capability_identifier_is_not_a_declaration() {
    // `capability_count` starts with the keyword but is not one.
    parse_module("capability_count stuff;\nfn f() -> i32 { return 0; }\n")
        .expect("an identifier that merely starts with `capability` is skipped");
}

#[test]
fn examples_without_capabilities_still_parse() {
    for ex in [
        include_str!("../../../examples/01-single-module.twasm"),
        include_str!("../../../examples/03-ownership-linearity.twasm"),
    ] {
        parse_module(ex).expect("examples declare no capabilities and must still parse");
    }
}
