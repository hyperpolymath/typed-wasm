// SPDX-License-Identifier: MPL-2.0
//
// `typedwasm.ownership` custom-section codec.
//
// Wire format (little-endian, byte-aligned):
//
//   u32le  count
//   for each entry:
//     u32le  func_idx
//     u8     n_params
//     u8[n]  param_kinds  (0=Unrestricted, 1=Linear, 2=SharedBorrow, 3=ExclBorrow)
//     u8     ret_kind
//
// Rust port of `Tw_verify.parse_ownership_section_payload` plus the
// inverse encoder mirroring `Codegen.build_ownership_section`. The OCaml
// parser is lenient on truncation — reading past the buffer end yields
// 0 — and this port matches that behaviour so the cross-compat suite
// (C5) sees identical results on every payload the OCaml side accepts.

use crate::OwnershipKind;

/// One entry in the ownership section: a function's index plus its
/// ownership-annotated signature. Mirrors the 3-tuple
/// `(int * ownership_kind list * ownership_kind)` returned by the OCaml
/// parser, but as a named struct for readability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipEntry {
    pub func_idx: u32,
    pub param_kinds: Vec<OwnershipKind>,
    pub ret_kind: OwnershipKind,
}

/// Parse the `typedwasm.ownership` custom-section payload into
/// structured entries.
///
/// Matches OCaml `Tw_verify.parse_ownership_section_payload` exactly,
/// including the leniency: a truncated payload yields zeros for the
/// missing bytes (interpreted as `Unrestricted` kinds and `func_idx = 0`).
/// A properly-emitted section will never be truncated; this leniency is
/// a defence-in-depth choice that preserves cross-impl parity.
pub fn parse_ownership_section_payload(payload: &[u8]) -> Vec<OwnershipEntry> {
    let mut r = LenientReader::new(payload);
    let count = r.read_u32_le();
    (0..count)
        .map(|_| {
            let func_idx = r.read_u32_le();
            let n_params = r.read_u8();
            let param_kinds = (0..n_params)
                .map(|_| OwnershipKind::from_byte(r.read_u8()))
                .collect();
            let ret_kind = OwnershipKind::from_byte(r.read_u8());
            OwnershipEntry {
                func_idx,
                param_kinds,
                ret_kind,
            }
        })
        .collect()
}

/// Encode entries to the `typedwasm.ownership` custom-section
/// payload format. The inverse of `parse_ownership_section_payload` for
/// any input that doesn't truncate.
///
/// Mirrors OCaml `Codegen.build_ownership_section` (which lives in the
/// affinescript repo and isn't visible here, but the wire format is the
/// authoritative spec).
///
/// # Panics
///
/// Panics if any entry has more than 255 params (the n_params field is
/// a single byte). Real wasm modules don't have functions with more
/// than 255 params (the engine limit is far lower), so this is
/// unreachable in practice.
pub fn build_ownership_section_payload(entries: &[OwnershipEntry]) -> Vec<u8> {
    let count: u32 = entries
        .len()
        .try_into()
        .expect("entry count must fit in u32");
    let mut out = Vec::with_capacity(4 + entries.len() * 8);
    out.extend_from_slice(&count.to_le_bytes());
    for entry in entries {
        out.extend_from_slice(&entry.func_idx.to_le_bytes());
        let n_params: u8 = entry
            .param_kinds
            .len()
            .try_into()
            .expect("param count must fit in u8");
        out.push(n_params);
        for k in &entry.param_kinds {
            out.push(k.to_byte());
        }
        out.push(entry.ret_kind.to_byte());
    }
    out
}

/// Cursor that reads u32le / u8 from a byte slice, returning 0 past EOF.
/// Mirrors the OCaml `read_u32_le` / `read_u8` helpers.
struct LenientReader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> LenientReader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    fn read_u32_le(&mut self) -> u32 {
        if self.pos + 4 > self.buf.len() {
            return 0;
        }
        let b = &self.buf[self.pos..self.pos + 4];
        self.pos += 4;
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }

    fn read_u8(&mut self) -> u8 {
        if self.pos >= self.buf.len() {
            return 0;
        }
        let v = self.buf[self.pos];
        self.pos += 1;
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use OwnershipKind::*;

    fn entry(func_idx: u32, params: Vec<OwnershipKind>, ret: OwnershipKind) -> OwnershipEntry {
        OwnershipEntry {
            func_idx,
            param_kinds: params,
            ret_kind: ret,
        }
    }

    #[test]
    fn empty_payload_yields_no_entries() {
        assert_eq!(parse_ownership_section_payload(&[]), vec![]);
    }

    #[test]
    fn count_zero_yields_no_entries() {
        assert_eq!(parse_ownership_section_payload(&[0, 0, 0, 0]), vec![]);
    }

    #[test]
    fn single_entry_no_params() {
        // count=1, func_idx=7, n_params=0, ret_kind=0
        let payload = [1, 0, 0, 0, 7, 0, 0, 0, 0, 0];
        let parsed = parse_ownership_section_payload(&payload);
        assert_eq!(parsed, vec![entry(7, vec![], Unrestricted)]);
    }

    #[test]
    fn single_entry_with_all_kinds() {
        // count=1, func_idx=42, n_params=4, params=[Linear, Unrestricted, ExclBorrow, SharedBorrow], ret=Linear
        let payload = [1, 0, 0, 0, 42, 0, 0, 0, 4, 1, 0, 3, 2, 1];
        let parsed = parse_ownership_section_payload(&payload);
        assert_eq!(
            parsed,
            vec![entry(
                42,
                vec![Linear, Unrestricted, ExclBorrow, SharedBorrow],
                Linear
            )]
        );
    }

    #[test]
    fn multiple_entries() {
        let entries = vec![
            entry(1, vec![Linear], Unrestricted),
            entry(2, vec![ExclBorrow, ExclBorrow], Linear),
            entry(99, vec![], SharedBorrow),
        ];
        let bytes = build_ownership_section_payload(&entries);
        assert_eq!(parse_ownership_section_payload(&bytes), entries);
    }

    #[test]
    fn unknown_kind_byte_decodes_to_unrestricted() {
        // Matches OCaml `kind_of_byte` fallback for cross-impl parity.
        // count=1, func_idx=0, n_params=1, param=99, ret=200
        let payload = [1, 0, 0, 0, 0, 0, 0, 0, 1, 99, 200];
        let parsed = parse_ownership_section_payload(&payload);
        assert_eq!(parsed, vec![entry(0, vec![Unrestricted], Unrestricted)]);
    }

    #[test]
    fn truncated_payload_reads_zeros_past_end() {
        // count=2, but only one entry's worth of bytes follows.
        // Matches OCaml leniency (returns 0 for short reads).
        // count=2, then func_idx=5, n_params=1, param=1 (Linear), ret=2 (SharedBorrow)
        // ... then nothing — second entry should read all zeros.
        let payload = [2, 0, 0, 0, 5, 0, 0, 0, 1, 1, 2];
        let parsed = parse_ownership_section_payload(&payload);
        assert_eq!(
            parsed,
            vec![
                entry(5, vec![Linear], SharedBorrow),
                entry(0, vec![], Unrestricted), // zero-filled
            ]
        );
    }

    #[test]
    fn roundtrip_empty() {
        let entries: Vec<OwnershipEntry> = vec![];
        let bytes = build_ownership_section_payload(&entries);
        assert_eq!(bytes, vec![0, 0, 0, 0]);
        assert_eq!(parse_ownership_section_payload(&bytes), entries);
    }

    #[test]
    fn roundtrip_realistic() {
        // Realistic shape: an exported `consume_string(s: own String) -> ()`
        // and a `borrow_string(s: ref String) -> i32`, both at indices the
        // affinescript codegen would produce after the host imports.
        let entries = vec![
            entry(2, vec![Linear], Unrestricted),
            entry(3, vec![SharedBorrow], Unrestricted),
        ];
        let bytes = build_ownership_section_payload(&entries);
        let parsed = parse_ownership_section_payload(&bytes);
        assert_eq!(parsed, entries);
    }

    #[test]
    fn build_emits_correct_wire_format() {
        let entries = vec![entry(7, vec![Linear, ExclBorrow], SharedBorrow)];
        let bytes = build_ownership_section_payload(&entries);
        // count=1, func_idx=7, n_params=2, params=[1,3], ret=2
        assert_eq!(bytes, vec![1, 0, 0, 0, 7, 0, 0, 0, 2, 1, 3, 2]);
    }
}

// ----------------------------------------------------------------------
// L2 region/schema carrier — `typedwasm.regions` custom section
//
// Pre-staged against typed-wasm proposal 0001 (typed-wasm#76, refs #34).
// UNSTABLE: the wire format here may change before the proposal moves to
// [accepted].
//
// Wire format (little-endian, byte-aligned, lenient on truncation —
// matches the LenientReader pattern used by ownership):
//
//   u16le   version              (= REGIONS_SECTION_VERSION = 1)
//   u32le   region_count
//   for each region (in index order, 0..region_count-1):
//       u32le  name_len
//       u8[]   name              (UTF-8, no NUL terminator)
//       u32le  field_count
//       for each field (in declaration order):
//           u32le  field_name_len
//           u8[]   field_name    (UTF-8)
//           u8     kind          (0=Scalar, 1=PtrOwning, 2=PtrBorrow, 3=PtrExclusive)
//           u8     wasm_ty       (0..10 = U8..WBool, 0xFF = N/A for ptr kinds)
//           u32le  target_region (0xFFFFFFFF if Scalar; else index into region table)
//           u8     nullability   (0=NonNull, 1=Nullable)
//           u32le  cardinality   (1=single, n>1=fixed array, 0=unbounded/dynamic)
//       u32le  region_byte_size  (sum-check; verifier may compare to its own calc)
//
// L15 capabilities (`typedwasm.capabilities`) and the access-site mapping
// from wasm `memarg` back to (region, field) are out of scope of this
// pre-stage. The access-site carrier is the open question discovered
// during pre-staging — see typed-wasm proposal §Open Questions.
// ----------------------------------------------------------------------

#[cfg(feature = "unstable-l2")]
pub const REGIONS_SECTION_VERSION: u16 = 1;

/// Pointer kind / scalar discriminant per `Pointer.idr::PtrKind` plus a
/// `Scalar` variant for non-pointer fields. One byte on the wire.
#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldKind {
    Scalar = 0,
    PtrOwning = 1,
    PtrBorrow = 2,
    PtrExclusive = 3,
}

#[cfg(feature = "unstable-l2")]
impl FieldKind {
    /// Lenient decode: unknown bytes fall back to `Scalar`. Matches the
    /// ownership-codec convention so cross-impl parity holds even when
    /// a future producer emits a new kind a v1 verifier doesn't know.
    pub fn from_byte(b: u8) -> Self {
        match b {
            1 => FieldKind::PtrOwning,
            2 => FieldKind::PtrBorrow,
            3 => FieldKind::PtrExclusive,
            _ => FieldKind::Scalar,
        }
    }

    pub fn to_byte(self) -> u8 {
        self as u8
    }
}

/// Wasm value/storage type per `Region.idr::WasmType`. One byte on the
/// wire. `NotApplicable` (0xFF) is emitted when the field's `kind` is a
/// pointer variant — the field-type semantics come from the target
/// region, not from a scalar wasm type.
#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WasmTy {
    U8 = 0,
    U16 = 1,
    U32 = 2,
    U64 = 3,
    I8 = 4,
    I16 = 5,
    I32 = 6,
    I64 = 7,
    F32 = 8,
    F64 = 9,
    WBool = 10,
    NotApplicable = 0xFF,
}

#[cfg(feature = "unstable-l2")]
impl WasmTy {
    /// Lenient decode: an unknown byte falls back to `NotApplicable`
    /// rather than panicking, so a v1 verifier silently downgrades on
    /// future reserved encodings.
    pub fn from_byte(b: u8) -> Self {
        match b {
            0 => WasmTy::U8,
            1 => WasmTy::U16,
            2 => WasmTy::U32,
            3 => WasmTy::U64,
            4 => WasmTy::I8,
            5 => WasmTy::I16,
            6 => WasmTy::I32,
            7 => WasmTy::I64,
            8 => WasmTy::F32,
            9 => WasmTy::F64,
            10 => WasmTy::WBool,
            _ => WasmTy::NotApplicable,
        }
    }

    pub fn to_byte(self) -> u8 {
        self as u8
    }
}

#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Nullability {
    NonNull = 0,
    Nullable = 1,
}

#[cfg(feature = "unstable-l2")]
impl Nullability {
    /// Lenient decode: only `1` decodes as `Nullable`; everything else
    /// is `NonNull`. Means a future producer that emits some new
    /// nullability encoding gets the safer interpretation on a v1
    /// verifier.
    pub fn from_byte(b: u8) -> Self {
        match b {
            1 => Nullability::Nullable,
            _ => Nullability::NonNull,
        }
    }

    pub fn to_byte(self) -> u8 {
        self as u8
    }
}

#[cfg(feature = "unstable-l2")]
pub const NO_TARGET_REGION: u32 = 0xFFFF_FFFF;

#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldEntry {
    pub name: String,
    pub kind: FieldKind,
    pub wasm_ty: WasmTy,
    /// Index into the enclosing section's region table. `NO_TARGET_REGION`
    /// (0xFFFFFFFF) when `kind == Scalar`.
    pub target_region: u32,
    pub nullability: Nullability,
    /// 1 = single value, n>1 = fixed-length array, 0 = unbounded /
    /// dynamic-bounds (verifier downgrades L5 to "needs runtime check").
    pub cardinality: u32,
}

#[cfg(feature = "unstable-l2")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionEntry {
    pub name: String,
    pub fields: Vec<FieldEntry>,
    /// Producer-declared total byte size. Redundant w.r.t. fields; the
    /// verifier may cross-check.
    pub region_byte_size: u32,
}

/// Parse the `typedwasm.regions` custom-section payload. Lenient on
/// truncation (matches the ownership codec): a short read returns zero
/// bytes, which round-trip to "no further regions/fields" rather than
/// erroring. The reader stops if `version != REGIONS_SECTION_VERSION` —
/// future major bumps belong in a new public API.
#[cfg(feature = "unstable-l2")]
pub fn parse_regions_section_payload(payload: &[u8]) -> Option<Vec<RegionEntry>> {
    let mut r = LenientReader::new(payload);
    let version = read_u16_le(&mut r);
    if version != REGIONS_SECTION_VERSION {
        return None;
    }
    let region_count = r.read_u32_le();
    let mut regions = Vec::with_capacity(region_count as usize);
    for _ in 0..region_count {
        let name = read_utf8(&mut r);
        let field_count = r.read_u32_le();
        let mut fields = Vec::with_capacity(field_count as usize);
        for _ in 0..field_count {
            let field_name = read_utf8(&mut r);
            let kind = FieldKind::from_byte(r.read_u8());
            let wasm_ty = WasmTy::from_byte(r.read_u8());
            let target_region = r.read_u32_le();
            let nullability = Nullability::from_byte(r.read_u8());
            let cardinality = r.read_u32_le();
            fields.push(FieldEntry {
                name: field_name,
                kind,
                wasm_ty,
                target_region,
                nullability,
                cardinality,
            });
        }
        let region_byte_size = r.read_u32_le();
        regions.push(RegionEntry {
            name,
            fields,
            region_byte_size,
        });
    }
    Some(regions)
}

/// Encode regions to the `typedwasm.regions` payload format.
/// `parse(build(x)) == Some(x)` for any input whose name byte lengths
/// fit in `u32` and whose field/region counts fit in `u32`.
#[cfg(feature = "unstable-l2")]
pub fn build_regions_section_payload(regions: &[RegionEntry]) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 + 4 + regions.len() * 32);
    out.extend_from_slice(&REGIONS_SECTION_VERSION.to_le_bytes());
    let region_count: u32 = regions
        .len()
        .try_into()
        .expect("region count must fit in u32");
    out.extend_from_slice(&region_count.to_le_bytes());
    for region in regions {
        write_utf8(&mut out, &region.name);
        let field_count: u32 = region
            .fields
            .len()
            .try_into()
            .expect("field count must fit in u32");
        out.extend_from_slice(&field_count.to_le_bytes());
        for field in &region.fields {
            write_utf8(&mut out, &field.name);
            out.push(field.kind.to_byte());
            out.push(field.wasm_ty.to_byte());
            out.extend_from_slice(&field.target_region.to_le_bytes());
            out.push(field.nullability.to_byte());
            out.extend_from_slice(&field.cardinality.to_le_bytes());
        }
        out.extend_from_slice(&region.region_byte_size.to_le_bytes());
    }
    out
}

#[cfg(feature = "unstable-l2")]
fn read_u16_le(r: &mut LenientReader<'_>) -> u16 {
    let lo = r.read_u8();
    let hi = r.read_u8();
    u16::from_le_bytes([lo, hi])
}

#[cfg(feature = "unstable-l2")]
fn read_utf8(r: &mut LenientReader<'_>) -> String {
    let len = r.read_u32_le() as usize;
    let mut bytes = Vec::with_capacity(len);
    for _ in 0..len {
        bytes.push(r.read_u8());
    }
    // Producers MUST emit valid UTF-8; lenient policy here is to drop
    // bad bytes rather than fail the whole section parse (matches the
    // truncation-tolerant style of the ownership codec).
    String::from_utf8_lossy(&bytes).into_owned()
}

#[cfg(feature = "unstable-l2")]
fn write_utf8(out: &mut Vec<u8>, s: &str) {
    let bytes = s.as_bytes();
    let len: u32 = bytes.len().try_into().expect("name length must fit in u32");
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(bytes);
}

#[cfg(all(test, feature = "unstable-l2"))]
mod regions_tests {
    use super::*;

    fn scalar_field(name: &str, ty: WasmTy, cardinality: u32) -> FieldEntry {
        FieldEntry {
            name: name.to_string(),
            kind: FieldKind::Scalar,
            wasm_ty: ty,
            target_region: NO_TARGET_REGION,
            nullability: Nullability::NonNull,
            cardinality,
        }
    }

    fn ptr_field(name: &str, kind: FieldKind, target: u32, nullable: bool) -> FieldEntry {
        FieldEntry {
            name: name.to_string(),
            kind,
            wasm_ty: WasmTy::NotApplicable,
            target_region: target,
            nullability: if nullable {
                Nullability::Nullable
            } else {
                Nullability::NonNull
            },
            cardinality: 1,
        }
    }

    #[test]
    fn empty_payload_yields_no_regions() {
        // Empty payload reads version=0, which is not the current version;
        // parser returns None to signal "unsupported".
        assert_eq!(parse_regions_section_payload(&[]), None);
    }

    #[test]
    fn version_only_yields_zero_regions() {
        let mut payload = REGIONS_SECTION_VERSION.to_le_bytes().to_vec();
        payload.extend_from_slice(&0u32.to_le_bytes());
        assert_eq!(parse_regions_section_payload(&payload), Some(vec![]));
    }

    #[test]
    fn wrong_version_returns_none() {
        let payload = [99u8, 0, 0, 0, 0, 0];
        assert_eq!(parse_regions_section_payload(&payload), None);
    }

    #[test]
    fn roundtrip_single_scalar_region() {
        let regions = vec![RegionEntry {
            name: "Player".to_string(),
            fields: vec![
                scalar_field("hp", WasmTy::I32, 1),
                scalar_field("speed", WasmTy::F64, 1),
            ],
            region_byte_size: 12,
        }];
        let bytes = build_regions_section_payload(&regions);
        assert_eq!(parse_regions_section_payload(&bytes), Some(regions));
    }

    #[test]
    fn roundtrip_ptr_field_with_foreign_key() {
        let regions = vec![
            RegionEntry {
                name: "Vec2".to_string(),
                fields: vec![
                    scalar_field("x", WasmTy::F32, 1),
                    scalar_field("y", WasmTy::F32, 1),
                ],
                region_byte_size: 8,
            },
            RegionEntry {
                name: "Enemy".to_string(),
                fields: vec![
                    scalar_field("hp", WasmTy::I32, 1),
                    ptr_field("pos", FieldKind::PtrOwning, 0, false),
                    ptr_field("target", FieldKind::PtrBorrow, 0, true),
                ],
                region_byte_size: 12,
            },
        ];
        let bytes = build_regions_section_payload(&regions);
        let parsed = parse_regions_section_payload(&bytes).expect("parses");
        assert_eq!(parsed, regions);
        // Sanity: the Enemy.target field round-trips as Nullable PtrBorrow → Vec2.
        let enemy = &parsed[1];
        assert_eq!(enemy.fields[2].kind, FieldKind::PtrBorrow);
        assert_eq!(enemy.fields[2].nullability, Nullability::Nullable);
        assert_eq!(enemy.fields[2].target_region, 0);
    }

    #[test]
    fn roundtrip_array_cardinality() {
        let regions = vec![RegionEntry {
            name: "Inventory".to_string(),
            fields: vec![
                scalar_field("slots", WasmTy::U32, 16), // fixed 16-element array
                scalar_field("dynamic_buf", WasmTy::U8, 0), // unbounded → downgrade
            ],
            region_byte_size: 64,
        }];
        let bytes = build_regions_section_payload(&regions);
        let parsed = parse_regions_section_payload(&bytes).expect("parses");
        assert_eq!(parsed, regions);
        assert_eq!(parsed[0].fields[0].cardinality, 16);
        assert_eq!(parsed[0].fields[1].cardinality, 0);
    }

    #[test]
    fn unknown_kind_byte_decodes_to_scalar() {
        // Forge a payload with an unknown kind byte; verify lenient fallback.
        let regions = vec![RegionEntry {
            name: "R".to_string(),
            fields: vec![scalar_field("f", WasmTy::I32, 1)],
            region_byte_size: 4,
        }];
        let mut bytes = build_regions_section_payload(&regions);
        // Locate the kind byte: 2 (version) + 4 (region_count) + 4 (name_len)
        // + 1 ("R") + 4 (field_count) + 4 (field_name_len) + 1 ("f") = 20.
        // Then the very next byte is `kind`.
        bytes[20] = 99;
        let parsed = parse_regions_section_payload(&bytes).expect("parses");
        assert_eq!(parsed[0].fields[0].kind, FieldKind::Scalar);
    }

    #[test]
    fn truncated_payload_zero_fills_trailing_fields() {
        // Build a valid payload, then chop the tail. The lenient reader
        // returns 0 for the missing bytes, which decodes to NonNull /
        // cardinality=0 / etc. Verifier semantics handle the downgrade.
        let regions = vec![RegionEntry {
            name: "X".to_string(),
            fields: vec![scalar_field("f", WasmTy::I32, 7)],
            region_byte_size: 4,
        }];
        let full = build_regions_section_payload(&regions);
        let truncated = &full[..full.len() - 4]; // chop region_byte_size
        let parsed = parse_regions_section_payload(truncated).expect("parses");
        assert_eq!(parsed[0].fields[0].cardinality, 7);
        // region_byte_size missing → reads as 0
        assert_eq!(parsed[0].region_byte_size, 0);
    }

    #[test]
    fn enum_byte_roundtrip() {
        for (b, k) in [
            (0, FieldKind::Scalar),
            (1, FieldKind::PtrOwning),
            (2, FieldKind::PtrBorrow),
            (3, FieldKind::PtrExclusive),
        ] {
            assert_eq!(FieldKind::from_byte(b), k);
            assert_eq!(k.to_byte(), b);
        }
        for b in 0u8..=10 {
            let ty = WasmTy::from_byte(b);
            assert_eq!(ty.to_byte(), b);
        }
        assert_eq!(WasmTy::from_byte(0xFF), WasmTy::NotApplicable);
        assert_eq!(Nullability::from_byte(0), Nullability::NonNull);
        assert_eq!(Nullability::from_byte(1), Nullability::Nullable);
        assert_eq!(Nullability::from_byte(42), Nullability::NonNull);
    }
}
