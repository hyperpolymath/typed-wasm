// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Build configuration for typed-wasm Zig FFI layer.
// Produces a C-ABI compatible library for region-typed memory operations.
//
// Updated for Zig 0.15+ API (addLibrary / createModule pattern).

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Shared module for the main library source
    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Main library — C-ABI compatible static library
    const lib = b.addLibrary(.{
        .name = "typed_wasm_ffi",
        .root_module = lib_mod,
        .linkage = .static,
    });
    b.installArtifact(lib);

    // WASM target — for self-hosting (typed-wasm checking typed-wasm)
    const wasm_lib = b.addLibrary(.{
        .name = "typed_wasm_ffi_wasm",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .wasm32,
                .os_tag = .wasi,
            }),
            .optimize = .ReleaseSmall,
        }),
        .linkage = .static,
    });
    b.installArtifact(wasm_lib);

    // Unit tests (embedded in main.zig)
    const main_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_main_tests = b.addRunArtifact(main_tests);
    const test_step = b.step("test", "Run FFI tests");
    test_step.dependOn(&run_main_tests.step);

    // Integration tests (if test directory exists)
    const integration_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/integration_test.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "typed_wasm", .module = lib_mod },
            },
        }),
    });
    const run_integration = b.addRunArtifact(integration_tests);
    const integration_step = b.step("integration", "Run integration tests");
    integration_step.dependOn(&run_integration.step);

    // ECHIDNA oracle tests (property-based verification)
    const oracle_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/echidna_oracle_test.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "typed_wasm", .module = lib_mod },
            },
        }),
    });
    const run_oracle = b.addRunArtifact(oracle_tests);
    const oracle_step = b.step("oracle", "Run ECHIDNA oracle property tests");
    oracle_step.dependOn(&run_oracle.step);

    // Also run oracle tests as part of the main test step
    test_step.dependOn(&run_oracle.step);
}
