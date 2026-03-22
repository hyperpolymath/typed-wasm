// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Oracle Tests for typed-wasm
//
// Property-based tests verifying the typed-wasm runtime against its
// specification. These form the "oracle" that ECHIDNA can use to
// check that the Idris2 proofs correspond to actual runtime behavior.
//
// Properties tested:
//   P1. Region allocation/deallocation lifecycle
//   P2. Typed access roundtrip (store then load preserves value)
//   P3. Bounds checking (out-of-range field index is rejected)
//   P4. Borrow tracking (double mutable borrow is prevented)
//   P5. Schema verification (same-shape ↔ compatible)
//   P6. Use-after-free prevention
//   P7. Determinism (same inputs → same outputs)

const std = @import("std");
const tw = @import("typed_wasm");
const testing = std.testing;
const RegionError = tw.RegionError;

// ============================================================================
// Helpers
// ============================================================================

// Create a test schema with N i32 fields
fn makeTestSchema(field_count: u16) tw.RegionSchema {
    const static_fields = comptime blk: {
        var fields: [64]tw.FieldDescriptor = undefined;
        for (0..64) |i| {
            fields[i] = .{
                .offset = @intCast(i * 4),
                .size = 4,
                .field_type = .i32,
                .nullable = false,
                .name = "field",
            };
        }
        break :blk fields;
    };
    return .{
        .schema_id = 0,
        .field_count = field_count,
        .instance_size = @as(u32, field_count) * 4,
        .alignment = 4,
        .fields = &static_fields,
        .instance_count = 1,
        .name = "test_schema",
    };
}

// ============================================================================
// P1: Region allocation/deallocation lifecycle
// ============================================================================

test "oracle P1: region alloc returns valid handle for valid schema" {
    var schema = makeTestSchema(4);
    const handle = tw.tw_region_alloc(&schema);
    try testing.expect(handle != 0);
    _ = tw.tw_region_free(handle);
}

test "oracle P1: region free returns ok for valid handle" {
    var schema = makeTestSchema(2);
    const handle = tw.tw_region_alloc(&schema);
    try testing.expect(handle != 0);
    const rc = tw.tw_region_free(handle);
    try testing.expectEqual(RegionError.ok, rc);
}

// ============================================================================
// P2: Typed access roundtrip
// ============================================================================

test "oracle P2: i32 store then load roundtrips" {
    var schema = makeTestSchema(4);
    const handle = tw.tw_region_alloc(&schema);
    defer _ = tw.tw_region_free(handle);

    const store_rc = tw.tw_region_set_i32(handle, 0, 42);
    try testing.expectEqual(RegionError.ok, store_rc);

    const result = tw.tw_region_get_i32(handle, 0);
    try testing.expectEqual(@as(i32, 42), result);
}

test "oracle P2: multiple fields are independent" {
    var schema = makeTestSchema(4);
    const handle = tw.tw_region_alloc(&schema);
    defer _ = tw.tw_region_free(handle);

    _ = tw.tw_region_set_i32(handle, 0, 100);
    _ = tw.tw_region_set_i32(handle, 1, 200);
    _ = tw.tw_region_set_i32(handle, 2, 300);

    try testing.expectEqual(@as(i32, 100), tw.tw_region_get_i32(handle, 0));
    try testing.expectEqual(@as(i32, 200), tw.tw_region_get_i32(handle, 1));
    try testing.expectEqual(@as(i32, 300), tw.tw_region_get_i32(handle, 2));
}

// ============================================================================
// P3: Bounds checking
// ============================================================================

test "oracle P3: out-of-bounds field index is rejected" {
    var schema = makeTestSchema(4);
    const handle = tw.tw_region_alloc(&schema);
    defer _ = tw.tw_region_free(handle);

    // Field index 4 is out of bounds for a 4-field region (0..3)
    const rc = tw.tw_region_set_i32(handle, 4, 99);
    try testing.expectEqual(RegionError.out_of_bounds, rc);
}

// ============================================================================
// P4: Borrow tracking
// ============================================================================

test "oracle P4: borrow acquire succeeds on fresh region" {
    var schema = makeTestSchema(2);
    const handle = tw.tw_region_alloc(&schema);
    defer _ = tw.tw_region_free(handle);

    const rc = tw.tw_region_borrow(handle);
    try testing.expectEqual(RegionError.ok, rc);
    _ = tw.tw_region_release(handle);
}

test "oracle P4: double mutable borrow is rejected" {
    var schema = makeTestSchema(2);
    const handle = tw.tw_region_alloc(&schema);
    defer _ = tw.tw_region_free(handle);

    const rc1 = tw.tw_region_borrow_mut(handle);
    try testing.expectEqual(RegionError.ok, rc1);

    // Second mutable borrow should fail
    const rc2 = tw.tw_region_borrow_mut(handle);
    try testing.expectEqual(RegionError.alias_violation, rc2);

    _ = tw.tw_region_release_mut(handle);
}

// ============================================================================
// P5: Schema verification
// ============================================================================

test "oracle P5: identical schemas are compatible" {
    var schema1 = makeTestSchema(3);
    var schema2 = makeTestSchema(3);

    const compat = tw.tw_schema_verify(&schema1, &schema2);
    try testing.expectEqual(@as(i32, 1), compat);
}

test "oracle P5: different-sized schemas are incompatible" {
    var schema1 = makeTestSchema(3);
    var schema2 = makeTestSchema(5);

    const compat = tw.tw_schema_verify(&schema1, &schema2);
    try testing.expectEqual(@as(i32, 0), compat);
}

// ============================================================================
// P6: Use-after-free prevention
// ============================================================================

test "oracle P6: access after free returns error" {
    var schema = makeTestSchema(1);
    const handle = tw.tw_region_alloc(&schema);
    _ = tw.tw_region_free(handle);

    // Store after free should fail
    const rc = tw.tw_region_set_i32(handle, 0, 42);
    try testing.expect(rc != RegionError.ok);
}

// ============================================================================
// P7: Determinism
// ============================================================================

test "oracle P7: same operations produce same results" {
    var schema = makeTestSchema(2);

    const r1 = tw.tw_region_alloc(&schema);
    const r2 = tw.tw_region_alloc(&schema);
    defer _ = tw.tw_region_free(r1);
    defer _ = tw.tw_region_free(r2);

    _ = tw.tw_region_set_i32(r1, 0, 777);
    _ = tw.tw_region_set_i32(r2, 0, 777);

    try testing.expectEqual(
        tw.tw_region_get_i32(r1, 0),
        tw.tw_region_get_i32(r2, 0),
    );
}
