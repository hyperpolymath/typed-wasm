// SPDX-License-Identifier: MPL-2.0
//
// Debug symbols via the wasm `name` section — Phase 1 deliverable 5 / #129
// (first increment). The full offset -> source-line source map is gated on
// source spans from the front-end -> IR seam (#127); this provides the
// function-name symbolication a debugger shows in stack traces.

use typed_wasm_codegen::{emit_example01, emit_example03};

fn name_section_strings(bytes: &[u8]) -> Option<String> {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CustomSection(c) = payload.expect("parse") {
            if c.name() == "name" {
                return Some(String::from_utf8_lossy(c.data()).into_owned());
            }
        }
    }
    None
}

#[test]
fn example01_emits_function_names() {
    let names = name_section_strings(&emit_example01())
        .expect("emitted module must carry a `name` custom section");
    for f in [
        "get_player_hp",
        "damage_player",
        "get_enemy_target_hp",
        "count_active_enemies",
        "move_player",
    ] {
        assert!(names.contains(f), "name section should include `{f}`");
    }
}

#[test]
fn example03_emits_function_names() {
    let names = name_section_strings(&emit_example03())
        .expect("emitted module must carry a `name` custom section");
    for f in ["despawn_particle", "update_particle", "read_particle_pos"] {
        assert!(names.contains(f), "name section should include `{f}`");
    }
}

#[test]
fn named_module_still_validates() {
    // The name section must not break full wasm validation.
    wasmparser::Validator::new()
        .validate_all(&emit_example01())
        .expect("module with a name section must validate");
}
