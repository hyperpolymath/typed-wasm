// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Build configuration for typed-wasm Zig FFI layer.
// Produces a C-ABI compatible library for region-typed memory operations.
//
// Updated for Zig 0.15+ API (addLibrary / createModule pattern).
// `link_libc` is set on every module: the FFI uses `std.heap.c_allocator`
// (malloc/free) so a C caller's `free()` matches the heap we allocate on —
// the correct allocator for a C-ABI boundary. Zig 0.15 requires the libc
// dependency to be declared explicitly.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Shared module for the main library source
    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });

    // Main library — C-ABI compatible static library
    const lib = b.addLibrary(.{
        .name = "typed_wasm_ffi",
        .root_module = lib_mod,
        .linkage = .static,
    });
    b.installArtifact(lib);

    // WASM target — for self-hosting (typed-wasm checking typed-wasm).
    // wasi provides libc (wasi-libc), so c_allocator works here too.
    const wasm_lib = b.addLibrary(.{
        .name = "typed_wasm_ffi_wasm",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .wasm32,
                .os_tag = .wasi,
            }),
            .optimize = .ReleaseSmall,
            .link_libc = true,
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
            .link_libc = true,
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
            .link_libc = true,
            .imports = &.{
                .{ .name = "typed_wasm", .module = lib_mod },
            },
        }),
    });
    const run_integration = b.addRunArtifact(integration_tests);
    const integration_step = b.step("integration", "Run integration tests");
    integration_step.dependOn(&run_integration.step);

    // ECHIDNA oracle tests (property-based verification).
    //
    // NOTE: these target a region-typed runtime API (`RegionSchema`,
    // `FieldDescriptor`, `RegionError`, typed load/store) that `src/main.zig`
    // does NOT yet implement — `main.zig` is currently the C-ABI skeleton
    // (init/free/process/string/array). The oracle suite is therefore
    // ASPIRATIONAL: it is kept available under its own `zig build oracle`
    // step so it documents the intended runtime contract, but it is
    // deliberately NOT wired into the default `zig build test` step (it would
    // fail to compile until the runtime lands). Tracked as the typed-wasm
    // region-runtime gap; do not silently "fix" it by stubbing the types.
    const oracle_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/echidna_oracle_test.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
            .imports = &.{
                .{ .name = "typed_wasm", .module = lib_mod },
            },
        }),
    });
    const run_oracle = b.addRunArtifact(oracle_tests);
    const oracle_step = b.step("oracle", "Run ECHIDNA oracle property tests (aspirational; needs the region runtime)");
    oracle_step.dependOn(&run_oracle.step);
    // Intentionally NOT: test_step.dependOn(&run_oracle.step) — see note above.
}
