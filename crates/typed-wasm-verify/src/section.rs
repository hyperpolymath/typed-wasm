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
