// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// The THIRD `typedwasm.ownership` producer — the language-agnosticism
// proof for typed-wasm as an independent compile target.
//
// AffineScript (OCaml) and Ephapax (Rust) emit the carrier from full
// compilers; the in-tree Rust codegen emits it from parsed `.twasm`.
// This producer shares NO ancestry with any of them: it hand-assembles
// a core wasm module byte-by-byte in Zig and attaches the ownership
// section per the wire format of `crates/typed-wasm-verify/src/section.rs`
// (u32le count; per entry u32le func_idx, u8 n_params, u8[n] param
// kinds, u8 ret kind; kinds: 0=Unrestricted, 1=Linear, 2=SharedBorrow,
// 3=ExclBorrow). If `typed-wasm-verify` accepts these bytes — and
// rejects the double-consume mutant — the contract is demonstrably
// producer-neutral, not an artefact of one toolchain's encoder.
//
// Fixture capture: `zig build gen-fixtures` writes
//   zig_clean_linear.wasm    — consume(x: Linear) uses its param once
//   zig_double_use.wasm      — the same function using it twice
// which are committed under
// `crates/typed-wasm-verify/tests/fixtures/zig_producer/` and pinned by
// `tests/third_producer_zig.rs` (accept / reject respectively).

const std = @import("std");

/// Emit a u32 as unsigned LEB128 (wasm's varuint32).
fn leb128(list: *std.ArrayList(u8), gpa: std.mem.Allocator, value: u32) !void {
    var v = value;
    while (true) {
        const byte: u8 = @intCast(v & 0x7F);
        v >>= 7;
        if (v == 0) {
            try list.append(gpa, byte);
            return;
        }
        try list.append(gpa, byte | 0x80);
    }
}

/// Append one section: id byte, LEB128 payload size, payload.
fn section(out: *std.ArrayList(u8), gpa: std.mem.Allocator, id: u8, payload: []const u8) !void {
    try out.append(gpa, id);
    try leb128(out, gpa, @intCast(payload.len));
    try out.appendSlice(gpa, payload);
}

/// The `typedwasm.ownership` payload for one function whose single
/// param is Linear (kind 1) and whose return is Unrestricted (kind 0).
/// Fixed-width little-endian per the typed-wasm carrier spec — NOT
/// LEB128; this is the cross-implementation parity surface.
fn ownershipPayload(out: *std.ArrayList(u8), gpa: std.mem.Allocator) !void {
    try out.appendSlice(gpa, &std.mem.toBytes(std.mem.nativeToLittle(u32, 1))); // count
    try out.appendSlice(gpa, &std.mem.toBytes(std.mem.nativeToLittle(u32, 0))); // func_idx
    try out.append(gpa, 1); // n_params
    try out.append(gpa, 1); // param 0: Linear
    try out.append(gpa, 0); // ret: Unrestricted
}

/// Build the complete module. `double_use` controls whether the body
/// consumes its Linear param once (honest) or twice (a wasm-level
/// double-free the verifier MUST reject).
pub fn buildModule(gpa: std.mem.Allocator, double_use: bool) ![]u8 {
    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(gpa);

    // Header: magic + version.
    try out.appendSlice(gpa, &.{ 0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00 });

    // Type section: one functype (param i32) -> ().
    var payload: std.ArrayList(u8) = .empty;
    defer payload.deinit(gpa);
    try payload.appendSlice(gpa, &.{ 0x01, 0x60, 0x01, 0x7F, 0x00 });
    try section(&out, gpa, 1, payload.items);

    // Function section: one function of type 0.
    payload.clearRetainingCapacity();
    try payload.appendSlice(gpa, &.{ 0x01, 0x00 });
    try section(&out, gpa, 3, payload.items);

    // Export section: "consume" -> func 0.
    payload.clearRetainingCapacity();
    const name = "consume";
    try payload.append(gpa, 0x01);
    try leb128(&payload, gpa, @intCast(name.len));
    try payload.appendSlice(gpa, name);
    try payload.appendSlice(gpa, &.{ 0x00, 0x00 }); // kind=func, idx=0
    try section(&out, gpa, 7, payload.items);

    // Code section: one body, no locals; `local.get 0; drop` once or twice.
    payload.clearRetainingCapacity();
    var body: std.ArrayList(u8) = .empty;
    defer body.deinit(gpa);
    try body.append(gpa, 0x00); // no local declarations
    const uses: usize = if (double_use) 2 else 1;
    for (0..uses) |_| {
        try body.appendSlice(gpa, &.{ 0x20, 0x00, 0x1A }); // local.get 0; drop
    }
    try body.append(gpa, 0x0B); // end
    try payload.append(gpa, 0x01); // one code entry
    try leb128(&payload, gpa, @intCast(body.items.len));
    try payload.appendSlice(gpa, body.items);
    try section(&out, gpa, 10, payload.items);

    // Custom section: typedwasm.ownership.
    payload.clearRetainingCapacity();
    const section_name = "typedwasm.ownership";
    try leb128(&payload, gpa, @intCast(section_name.len));
    try payload.appendSlice(gpa, section_name);
    try ownershipPayload(&payload, gpa);
    try section(&out, gpa, 0, payload.items);

    return out.toOwnedSlice(gpa);
}

/// Fixture generator: `twasm-producer <output-dir>`.
pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    var args = try std.process.argsWithAllocator(gpa);
    defer args.deinit();
    _ = args.next(); // argv[0]
    const dir_path = args.next() orelse {
        std.debug.print("usage: twasm-producer <output-dir>\n", .{});
        return error.MissingOutputDir;
    };

    var dir = try std.fs.cwd().makeOpenPath(dir_path, .{});
    defer dir.close();

    inline for (.{ .{ "zig_clean_linear.wasm", false }, .{ "zig_double_use.wasm", true } }) |spec| {
        const bytes = try buildModule(gpa, spec[1]);
        defer gpa.free(bytes);
        try dir.writeFile(.{ .sub_path = spec[0], .data = bytes });
        std.debug.print("wrote {s}/{s} ({d} bytes)\n", .{ dir_path, spec[0], bytes.len });
    }
}

test "module bytes start with wasm magic + version" {
    const bytes = try buildModule(std.testing.allocator, false);
    defer std.testing.allocator.free(bytes);
    try std.testing.expectEqualSlices(
        u8,
        &.{ 0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00 },
        bytes[0..8],
    );
}

test "clean and double-use differ only in the code section" {
    const clean = try buildModule(std.testing.allocator, false);
    defer std.testing.allocator.free(clean);
    const double = try buildModule(std.testing.allocator, true);
    defer std.testing.allocator.free(double);
    // One extra `local.get 0; drop` = 3 bytes.
    try std.testing.expectEqual(clean.len + 3, double.len);
}

test "ownership section is present with the Linear kind byte" {
    const bytes = try buildModule(std.testing.allocator, false);
    defer std.testing.allocator.free(bytes);
    const needle = "typedwasm.ownership";
    const at = std.mem.indexOf(u8, bytes, needle) orelse return error.SectionMissing;
    // Payload follows the name: count=1 u32le, func_idx=0 u32le,
    // n_params=1, kind=Linear(1), ret=Unrestricted(0).
    const payload = bytes[at + needle.len ..];
    try std.testing.expectEqualSlices(
        u8,
        &.{ 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0 },
        payload[0..11],
    );
}

test "generator is deterministic" {
    const a = try buildModule(std.testing.allocator, false);
    defer std.testing.allocator.free(a);
    const b = try buildModule(std.testing.allocator, false);
    defer std.testing.allocator.free(b);
    try std.testing.expectEqualSlices(u8, a, b);
}
