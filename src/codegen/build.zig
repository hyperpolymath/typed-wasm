// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Build configuration for `twasmc` — the typed-wasm codegen v0 producer
// (the "Code generator | Zig -> Wasm" architecture component).
//
// Targets Zig 0.16.0 (std.Io reorg + unmanaged ArrayList). Reproduce the
// toolchain with `pip install ziglang==0.16.0` (`python -m ziglang`), or a
// matching standalone Zig 0.16.0.
//
//   zig build                 # produces zig-out/bin/twasmc
//   zig build run < in.twasm   > out.wasm

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe = b.addExecutable(.{
        .name = "twasmc",
        .root_module = exe_mod,
    });
    b.installArtifact(exe);

    const run = b.addRunArtifact(exe);
    if (b.args) |args| run.addArgs(args);
    const run_step = b.step("run", "Run twasmc (reads .twasm on stdin, emits .wasm on stdout)");
    run_step.dependOn(&run.step);
}
