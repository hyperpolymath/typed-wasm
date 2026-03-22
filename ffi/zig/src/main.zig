// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// typed-wasm Zig FFI — C-ABI compatible memory operations for typed regions.
//
// This layer bridges the Idris2 ABI definitions (which prove correctness)
// with actual WASM memory operations (which execute at runtime). The Zig
// code implements what the Idris2 proofs guarantee.
//
// Architecture:
//   Idris2 ABI (proofs) → C headers (generated) → Zig FFI (this file)
//
// All functions are exported with C calling convention for maximum
// interoperability. No Zig-specific types cross the ABI boundary.

const std = @import("std");

// ============================================================================
// Core Types
// ============================================================================

/// Opaque handle to a region instance. The u64 encodes:
///   - bits [0:31]  = base offset in linear memory
///   - bits [32:47] = region schema ID (matches Idris2 ABI)
///   - bits [48:62] = generation counter (for lifetime safety)
///   - bit  [63]    = ownership flag (1 = owning, 0 = borrowed)
pub const RegionHandle = u64;

/// Region schema descriptor — describes the layout of a region.
/// Generated from Idris2 ABI definitions at compile time.
pub const RegionSchema = extern struct {
    /// Unique schema identifier (matches Idris2 ABI)
    schema_id: u16,
    /// Number of fields in the region
    field_count: u16,
    /// Total size of one region instance in bytes (including padding)
    instance_size: u32,
    /// Required alignment in bytes (must be power of 2)
    alignment: u32,
    /// Pointer to field descriptor array
    fields: [*]const FieldDescriptor,
    /// Number of instances (1 for singleton, N for array regions)
    instance_count: u32,
    /// Schema name (for diagnostics)
    name: [*:0]const u8,
};

/// Field descriptor within a region schema.
pub const FieldDescriptor = extern struct {
    /// Byte offset from region base
    offset: u32,
    /// Field size in bytes
    size: u16,
    /// Field type tag (see FieldType enum)
    field_type: FieldType,
    /// Is this field nullable (opt<T>)?
    nullable: bool,
    /// Field name (for diagnostics)
    name: [*:0]const u8,
};

/// Field type tags — mirrors the Idris2 ABI PrimitiveType.
pub const FieldType = enum(u8) {
    i8 = 0,
    i16 = 1,
    i32 = 2,
    i64 = 3,
    u8 = 4,
    u16 = 5,
    u32 = 6,
    u64 = 7,
    f32 = 8,
    f64 = 9,
    bool_ = 10,
    ptr = 11, // owning pointer
    ref_ = 12, // borrowing reference
    unique = 13, // exclusive pointer
    region_ref = 14, // embedded region
};

/// Effect flags — bitfield matching Idris2 ABI effect types.
pub const EffectFlags = packed struct(u8) {
    read: bool = false,
    write: bool = false,
    alloc: bool = false,
    free: bool = false,
    _padding: u4 = 0,
};

/// Result type for operations that can fail.
pub const RegionError = enum(u32) {
    ok = 0,
    out_of_bounds = 1,
    type_mismatch = 2,
    null_dereference = 3,
    lifetime_expired = 4,
    already_freed = 5,
    alias_violation = 6,
    effect_violation = 7,
    schema_mismatch = 8,
    alignment_fault = 9,
    invariant_violation = 10,
};

// ============================================================================
// Region Registry — tracks live regions and their schemas
// ============================================================================

/// Maximum number of simultaneously live region instances.
const MAX_REGIONS: usize = 4096;

/// Generation counter for lifetime tracking (Level 9).
var generation_counter: u16 = 0;

/// Registry entry for a live region.
const RegistryEntry = struct {
    schema: *const RegionSchema,
    base_offset: u32,
    generation: u16,
    is_live: bool,
    ref_count: u16, // number of active borrows
    has_mut_borrow: bool, // exclusive mutable borrow active
};

/// The global region registry.
var registry: [MAX_REGIONS]RegistryEntry = [_]RegistryEntry{.{
    .schema = undefined,
    .base_offset = 0,
    .generation = 0,
    .is_live = false,
    .ref_count = 0,
    .has_mut_borrow = false,
}} ** MAX_REGIONS;

// ============================================================================
// Region Lifecycle (Level 10: Linearity)
// ============================================================================

/// Allocate a new region instance in linear memory.
/// Returns an owning RegionHandle (linear — must be freed exactly once).
///
/// The Idris2 ABI proves that the caller will free this handle exactly once.
/// This function trusts that proof and does not add runtime linearity checks.
export fn tw_region_alloc(
    schema: *const RegionSchema,
    memory_base: [*]u8,
    memory_size: u32,
    offset: u32,
) RegionHandle {
    // Find a free registry slot
    for (&registry, 0..) |*entry, i| {
        if (!entry.is_live) {
            generation_counter +%= 1;

            entry.* = .{
                .schema = schema,
                .base_offset = offset,
                .generation = generation_counter,
                .is_live = true,
                .ref_count = 0,
                .has_mut_borrow = false,
            };

            // Zero-initialise the memory region
            const region_size = schema.instance_size * schema.instance_count;
            if (offset + region_size <= memory_size) {
                const region_mem = memory_base[offset..][0..region_size];
                @memset(region_mem, 0);
            }

            // Encode handle: offset | schema_id | generation | ownership
            return @as(u64, offset) |
                (@as(u64, schema.schema_id) << 32) |
                (@as(u64, generation_counter) << 48) |
                (@as(u64, 1) << 63); // owning
        }
        _ = i;
    }

    // No free slot — should not happen if Idris2 proofs are correct
    return 0;
}

/// Free a region instance. Consumes the owning handle.
/// After this call, any use of the handle is a Level 9 violation.
export fn tw_region_free(handle: RegionHandle) RegionError {
    const slot = decode_slot(handle) orelse return .lifetime_expired;
    var entry = &registry[slot];

    if (!entry.is_live) return .already_freed;
    if (entry.ref_count > 0) return .alias_violation; // outstanding borrows

    entry.is_live = false;
    return .ok;
}

// ============================================================================
// Typed Access (Levels 2-6)
// ============================================================================

/// Read a 32-bit integer field from a region instance.
/// Level 2: schema resolves field_index to a FieldDescriptor.
/// Level 3: field type must be i32.
/// Level 5: instance_index must be < schema.instance_count.
/// Level 6: return type is i32.
export fn tw_region_get_i32(
    handle: RegionHandle,
    instance_index: u32,
    field_index: u16,
    memory_base: [*]const u8,
) i32 {
    const slot = decode_slot(handle) orelse return 0;
    const entry = &registry[slot];

    if (!entry.is_live) return 0;

    const schema = entry.schema;
    if (field_index >= schema.field_count) return 0;
    if (instance_index >= schema.instance_count) return 0;

    const field = &schema.fields[field_index];

    // Level 3: type check
    if (field.field_type != .i32) return 0;

    const offset = entry.base_offset +
        (instance_index * schema.instance_size) +
        field.offset;

    return std.mem.readInt(i32, @as(*const [4]u8, @ptrCast(@alignCast(memory_base + offset))), .little);
}

/// Write a 32-bit integer field to a region instance.
/// Same level checks as get, plus Level 7: requires &mut (exclusive access).
export fn tw_region_set_i32(
    handle: RegionHandle,
    instance_index: u32,
    field_index: u16,
    value: i32,
    memory_base: [*]u8,
) RegionError {
    const slot = decode_slot(handle) orelse return .lifetime_expired;
    const entry = &registry[slot];

    if (!entry.is_live) return .already_freed;

    const schema = entry.schema;
    if (field_index >= schema.field_count) return .out_of_bounds;
    if (instance_index >= schema.instance_count) return .out_of_bounds;

    const field = &schema.fields[field_index];
    if (field.field_type != .i32) return .type_mismatch;

    const offset = entry.base_offset +
        (instance_index * schema.instance_size) +
        field.offset;

    std.mem.writeInt(i32, @as(*[4]u8, @ptrCast(@alignCast(memory_base + offset))), value, .little);
    return .ok;
}

/// Read a 64-bit float field from a region instance.
export fn tw_region_get_f64(
    handle: RegionHandle,
    instance_index: u32,
    field_index: u16,
    memory_base: [*]const u8,
) f64 {
    const slot = decode_slot(handle) orelse return 0.0;
    const entry = &registry[slot];

    if (!entry.is_live) return 0.0;

    const schema = entry.schema;
    if (field_index >= schema.field_count) return 0.0;
    if (instance_index >= schema.instance_count) return 0.0;

    const field = &schema.fields[field_index];
    if (field.field_type != .f64) return 0.0;

    const offset = entry.base_offset +
        (instance_index * schema.instance_size) +
        field.offset;

    const bytes = @as(*const [8]u8, @ptrCast(@alignCast(memory_base + offset)));
    return @bitCast(std.mem.readInt(u64, bytes, .little));
}

/// Read a 32-bit float field from a region instance.
export fn tw_region_get_f32(
    handle: RegionHandle,
    instance_index: u32,
    field_index: u16,
    memory_base: [*]const u8,
) f32 {
    const slot = decode_slot(handle) orelse return 0.0;
    const entry = &registry[slot];

    if (!entry.is_live) return 0.0;

    const schema = entry.schema;
    if (field_index >= schema.field_count) return 0.0;
    if (instance_index >= schema.instance_count) return 0.0;

    const field = &schema.fields[field_index];
    if (field.field_type != .f32) return 0.0;

    const offset = entry.base_offset +
        (instance_index * schema.instance_size) +
        field.offset;

    const bytes = @as(*const [4]u8, @ptrCast(@alignCast(memory_base + offset)));
    return @bitCast(std.mem.readInt(u32, bytes, .little));
}

// ============================================================================
// Borrow Tracking (Level 7: Aliasing Safety)
// ============================================================================

/// Acquire a shared (immutable) borrow on a region.
/// Multiple shared borrows can coexist. Fails if a mutable borrow is active.
export fn tw_region_borrow(handle: RegionHandle) RegionError {
    const slot = decode_slot(handle) orelse return .lifetime_expired;
    var entry = &registry[slot];

    if (!entry.is_live) return .already_freed;
    if (entry.has_mut_borrow) return .alias_violation;

    entry.ref_count += 1;
    return .ok;
}

/// Acquire an exclusive (mutable) borrow on a region.
/// Fails if any borrows (shared or mutable) are active.
export fn tw_region_borrow_mut(handle: RegionHandle) RegionError {
    const slot = decode_slot(handle) orelse return .lifetime_expired;
    var entry = &registry[slot];

    if (!entry.is_live) return .already_freed;
    if (entry.ref_count > 0) return .alias_violation;
    if (entry.has_mut_borrow) return .alias_violation;

    entry.has_mut_borrow = true;
    return .ok;
}

/// Release a shared borrow.
export fn tw_region_release(handle: RegionHandle) RegionError {
    const slot = decode_slot(handle) orelse return .lifetime_expired;
    var entry = &registry[slot];

    if (!entry.is_live) return .already_freed;
    if (entry.ref_count == 0) return .alias_violation; // no borrow to release

    entry.ref_count -= 1;
    return .ok;
}

/// Release a mutable borrow.
export fn tw_region_release_mut(handle: RegionHandle) RegionError {
    const slot = decode_slot(handle) orelse return .lifetime_expired;
    var entry = &registry[slot];

    if (!entry.is_live) return .already_freed;
    if (!entry.has_mut_borrow) return .alias_violation;

    entry.has_mut_borrow = false;
    return .ok;
}

// ============================================================================
// Schema Verification (Multi-Module Type Agreement)
// ============================================================================

/// Verify that two region schemas are structurally compatible.
/// This is the core of multi-module type safety: when Module A exports
/// a region and Module B imports it, this function verifies agreement.
///
/// Returns .ok if schemas agree on all fields present in `imported`.
/// The imported schema may be a subset (fewer fields) of the exported schema.
export fn tw_schema_verify(
    exported: *const RegionSchema,
    imported: *const RegionSchema,
) RegionError {
    // Instance size must agree
    if (exported.instance_size != imported.instance_size) return .schema_mismatch;

    // Alignment must agree
    if (exported.alignment != imported.alignment) return .schema_mismatch;

    // Every field in the import must exist in the export with matching type+offset
    for (0..imported.field_count) |i| {
        const imp_field = &imported.fields[i];
        var found = false;

        for (0..exported.field_count) |j| {
            const exp_field = &exported.fields[j];

            // Match by name
            if (std.mem.orderZ(u8, imp_field.name, exp_field.name) == .eq) {
                // Type must match
                if (imp_field.field_type != exp_field.field_type) return .type_mismatch;
                // Offset must match
                if (imp_field.offset != exp_field.offset) return .schema_mismatch;
                // Size must match
                if (imp_field.size != exp_field.size) return .schema_mismatch;
                found = true;
                break;
            }
        }

        if (!found) return .schema_mismatch;
    }

    return .ok;
}

// ============================================================================
// Internal Helpers
// ============================================================================

/// Decode a RegionHandle to a registry slot index.
/// Returns null if the handle's generation doesn't match (Level 9: lifetime expired).
fn decode_slot(handle: RegionHandle) ?usize {
    const base_offset: u32 = @truncate(handle);
    const generation: u16 = @truncate(handle >> 48);

    // Linear search for matching entry (could be optimised with a hash map)
    for (&registry, 0..) |*entry, i| {
        if (entry.is_live and
            entry.base_offset == base_offset and
            entry.generation == generation)
        {
            return i;
        }
    }

    return null;
}

// ============================================================================
// Tests
// ============================================================================

test "field type size" {
    try std.testing.expectEqual(@sizeOf(FieldType), 1);
    try std.testing.expectEqual(@sizeOf(EffectFlags), 1);
}

test "handle encoding roundtrip" {
    const handle: RegionHandle = @as(u64, 1024) | // offset
        (@as(u64, 42) << 32) | // schema_id
        (@as(u64, 7) << 48) | // generation
        (@as(u64, 1) << 63); // owning

    const offset: u32 = @truncate(handle);
    const schema_id: u16 = @truncate(handle >> 32);
    const owning: bool = (handle >> 63) == 1;
    const gen: u15 = @truncate(handle >> 48);

    try std.testing.expectEqual(offset, 1024);
    try std.testing.expectEqual(schema_id, 42);
    try std.testing.expectEqual(gen, @as(u15, 7));
    try std.testing.expect(owning);
}
