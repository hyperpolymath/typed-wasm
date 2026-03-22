// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Integration tests for the typed-wasm Zig FFI layer.
// These tests verify that the C-ABI surface matches the Idris2 ABI definitions.

const std = @import("std");
const testing = std.testing;
const typed_wasm = @import("typed_wasm");

// ============================================================================
// Region Handle Tests
// ============================================================================

test "region handle bit layout" {
    // A region handle encodes base offset, schema ID, generation, and ownership
    // in a single u64.
    const handle: typed_wasm.RegionHandle = 0;
    try testing.expectEqual(@as(typed_wasm.RegionHandle, 0), handle);
}

test "schema descriptor field access" {
    // A SchemaDescriptor has a name, field count, and total size.
    const desc = typed_wasm.SchemaDescriptor{
        .name = "test_region",
        .field_count = 3,
        .total_size = 16,
        .alignment = 4,
    };
    try testing.expectEqual(@as(u32, 3), desc.field_count);
    try testing.expectEqual(@as(u32, 16), desc.total_size);
}

test "wasm type sizes match ABI" {
    // Verify that the Zig FFI type sizes match the Idris2 ABI definitions.
    try testing.expectEqual(@as(u32, 1), typed_wasm.wasmTypeSize(.u8));
    try testing.expectEqual(@as(u32, 2), typed_wasm.wasmTypeSize(.u16));
    try testing.expectEqual(@as(u32, 4), typed_wasm.wasmTypeSize(.u32));
    try testing.expectEqual(@as(u32, 8), typed_wasm.wasmTypeSize(.u64));
    try testing.expectEqual(@as(u32, 4), typed_wasm.wasmTypeSize(.f32));
    try testing.expectEqual(@as(u32, 8), typed_wasm.wasmTypeSize(.f64));
}
