// SPDX-License-Identifier: MPL-2.0
//
// WAT (text wasm) emission — Phase 1 deliverable 4 (issue #125).
//
// WAT is a debugging view of the exact bytes the binary emitter produces,
// so these assertions pin that the text form (a) renders the module
// structure, (b) is a faithful print of the emitted bytes, and (c)
// surfaces the typedwasm.* carrier sections.

use typed_wasm_codegen::{emit_example01, emit_example01_wat, wat};

#[test]
fn wat_renders_module_memory_and_exports() {
    let text = emit_example01_wat();
    assert!(text.contains("(module"), "WAT must open a module");
    assert!(
        text.contains("(memory"),
        "WAT must declare the linear memory"
    );
    assert!(text.contains("(func"), "WAT must contain functions");
    // Export names survive into the text form.
    assert!(
        text.contains("get_player_hp"),
        "export name should appear in WAT"
    );
    assert!(
        text.contains("move_player"),
        "export name should appear in WAT"
    );
}

#[test]
fn wat_is_a_faithful_print_of_the_emitted_bytes() {
    let bytes = emit_example01();
    assert_eq!(wat(&bytes), emit_example01_wat());
}

#[test]
fn wat_surfaces_the_typed_carriers() {
    // wasmprinter renders unrecognised custom sections, so the carrier
    // names appear in the text — that is the point of WAT-for-debugging:
    // you can see the typed metadata next to the code.
    let text = emit_example01_wat();
    assert!(
        text.contains("typedwasm.regions"),
        "WAT should surface the typedwasm.regions carrier:\n{text}"
    );
    assert!(
        text.contains("typedwasm.access-sites"),
        "WAT should surface the typedwasm.access-sites carrier:\n{text}"
    );
}
