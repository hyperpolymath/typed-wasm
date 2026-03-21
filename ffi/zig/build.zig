// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Build configuration for typed-wasm Zig FFI layer.
// Produces a C-ABI compatible library for region-typed memory operations.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Main library — C-ABI compatible
    const lib = b.addStaticLibrary(.{
        .name = "typed_wasm_ffi",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(lib);

    // WASM target — for self-hosting (typed-wasm checking typed-wasm)
    const wasm_lib = b.addStaticLibrary(.{
        .name = "typed_wasm_ffi_wasm",
        .root_source_file = b.path("src/main.zig"),
        .target = b.resolveTargetQuery(.{
            .cpu_arch = .wasm32,
            .os_tag = .wasi,
        }),
        .optimize = .ReleaseSmall,
    });
    b.installArtifact(wasm_lib);

    // Tests
    const main_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    const run_main_tests = b.addRunArtifact(main_tests);
    const test_step = b.step("test", "Run FFI tests");
    test_step.dependOn(&run_main_tests.step);

    // Integration tests
    const integration_tests = b.addTest(.{
        .root_source_file = b.path("test/integration_test.zig"),
        .target = target,
        .optimize = optimize,
    });
    integration_tests.root_module.addImport("typed_wasm", &lib.root_module);
    const run_integration = b.addRunArtifact(integration_tests);
    const integration_step = b.step("integration", "Run integration tests");
    integration_step.dependOn(&run_integration.step);
}
