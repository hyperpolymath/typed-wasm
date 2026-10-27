// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! L15 resource capabilities: the surface checks for one module.
//!
//! The front-end ([`crate::parser`]) records the module's `capability NAME;`
//! declarations, each function's `caps: { … }` sub-clause and the names each
//! function body calls; [`check`] then enforces
//!
//! * **L15-A** (distinct): no capability is declared twice in the module;
//! * **L15-B** (well-scoped): every name in a function's `caps` set is a
//!   declared capability;
//! * **L15-C** (monotone): when F calls G in the same module, G's `caps` set
//!   is contained in F's.
//!
//! L15-C is checked per call site, as `ResourceCapabilities.idr` states it
//! (`WellFormedCall` carries `CallCompatible caller.required callee.required`).
//! Transitive calls need no separate check: `callCompose` proves that
//! well-formed edges compose. A function without a `caps` clause requires no
//! capabilities, so it may only call functions that require none.
//!
//! Scope: the top-level module. The front-end skips `module isolated … { … }`
//! bodies, so their declarations and functions are not checked here, and a
//! call to an imported function is not checked either (cross-module grants are
//! proposal 0004).

/// One function's L15 facts, as the front-end recorded them.
#[derive(Debug, Clone, Default)]
pub struct FnCaps {
    pub name: String,
    /// The `caps: { … }` names, in source order; empty when absent.
    pub caps: Vec<String>,
    /// Names the body calls (`name(…)`), in source order. Only names that are
    /// functions of this module take part in L15-C.
    pub calls: Vec<String>,
}

/// A lexical token: an identifier, or any other single non-space character.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Punct(char),
}

/// Split source text into identifiers and punctuation, dropping whitespace,
/// `//` and `/* */` comments and the contents of string literals, so a name
/// that only appears in a comment or a string is never taken for a call.
fn tokens(src: &str) -> Vec<Tok> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
        } else if c == b'/' && b.get(i + 1) == Some(&b'/') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else if c == b'/' && b.get(i + 1) == Some(&b'*') {
            i += 2;
            while i < b.len() && !(b[i] == b'*' && b.get(i + 1) == Some(&b'/')) {
                i += 1;
            }
            i = (i + 2).min(b.len());
        } else if c == b'"' {
            i += 1;
            while i < b.len() && b[i] != b'"' {
                i += if b[i] == b'\\' { 2 } else { 1 };
            }
            i = (i + 1).min(b.len());
            out.push(Tok::Punct('"'));
        } else if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            out.push(Tok::Ident(src[start..i].to_string()));
        } else {
            // Step over a whole UTF-8 character so slicing stays on a boundary.
            let ch = src[i..].chars().next().unwrap_or('\u{FFFD}');
            out.push(Tok::Punct(ch));
            i += ch.len_utf8();
        }
    }
    out
}

/// Collect call candidates in source order, retaining repeated names.
/// A candidate is an identifier followed by `(`,
/// unless it follows `.`, `$` or `@` (a field, region variable or region
/// reference). Comments and string contents are ignored. Keywords and
/// unresolved names are included; [`check`] resolves candidates against
/// the module's functions.
pub fn called_names(body: &str) -> Vec<String> {
    let toks = tokens(body);
    let mut out = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        if let Tok::Ident(name) = t {
            let prev_ok = i == 0
                || !matches!(
                    toks[i - 1],
                    Tok::Punct('.') | Tok::Punct('$') | Tok::Punct('@')
                );
            if prev_ok && toks.get(i + 1) == Some(&Tok::Punct('(')) {
                out.push(name.clone());
            }
        }
    }
    out
}

/// The `caps: { a, b }` sub-clause inside the text of an `effects { … }`
/// block (without its outer braces). `None` when the block has no `caps`
/// sub-clause (the flat `effects { Read, Write }` form).
/// Only the first `caps: {` is used; names are collected in source order,
/// retaining duplicates, until a token other than an identifier or comma.
/// An empty clause returns `Some` with an empty vector; closing braces and
/// separators are not validated.
pub fn caps_clause(effects_body: &str) -> Option<Vec<String>> {
    let toks = tokens(effects_body);
    let start = toks.windows(3).position(|w| {
        w[0] == Tok::Ident("caps".into()) && w[1] == Tok::Punct(':') && w[2] == Tok::Punct('{')
    })?;
    let mut caps = Vec::new();
    for t in &toks[start + 3..] {
        match t {
            Tok::Ident(name) => caps.push(name.clone()),
            Tok::Punct(',') => {}
            _ => break, // `}` closes the list
        }
    }
    Some(caps)
}

/// Run L15-A, L15-B and L15-C over one module. `declared` lists the
/// `capability` declarations in source order (duplicates included, so L15-A
/// can see them). Returns diagnostic strings grouped by L15-A, L15-B,
/// then L15-C, preserving input order within each rule; empty on success.
/// Calls absent from `funcs` are ignored. Each offending call produces one
/// L15-C diagnostic listing the callee's capabilities missing from the caller.
pub fn check(declared: &[String], funcs: &[FnCaps]) -> Vec<String> {
    let mut errors = Vec::new();
    let mut seen: Vec<&str> = Vec::new();
    for cap in declared {
        if seen.contains(&cap.as_str()) {
            errors.push(format!(
                "L15-A: capability '{cap}' is declared more than once in the module \
                 (capability declarations must be distinct)"
            ));
        } else {
            seen.push(cap);
        }
    }
    for f in funcs {
        for cap in &f.caps {
            if !seen.contains(&cap.as_str()) {
                errors.push(format!(
                    "L15-B: function '{}' requires capability '{cap}', which the module does \
                     not declare (add `capability {cap};`)",
                    f.name
                ));
            }
        }
    }
    for f in funcs {
        for callee in &f.calls {
            let Some(g) = funcs.iter().find(|g| &g.name == callee) else {
                continue; // not a function of this module
            };
            let missing: Vec<&str> = g
                .caps
                .iter()
                .filter(|c| !f.caps.contains(c))
                .map(String::as_str)
                .collect();
            if !missing.is_empty() {
                errors.push(format!(
                    "L15-C: function '{}' calls '{}', which requires capabilities {{ {} }} that \
                     '{}' does not hold (a caller's caps must contain its callee's)",
                    f.name,
                    g.name,
                    missing.join(", "),
                    f.name
                ));
            }
        }
    }
    errors
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calls_skip_comments_strings_and_fields() {
        let body = r#"
            // net_send(x) in a comment
            let s = "log(1)";
            let a = $p.helper(1);
            if (ready()) { return send(a, compute (2)); }
        "#;
        // `if (` is a candidate too; `check` drops it, since only the
        // module's own functions take part in L15-C.
        assert_eq!(called_names(body), ["if", "ready", "send", "compute"]);
    }

    #[test]
    fn caps_clause_forms() {
        assert_eq!(
            caps_clause(" memory: { Read }, caps: { net, fs } "),
            Some(vec!["net".to_string(), "fs".to_string()])
        );
        assert_eq!(caps_clause(" caps: { } "), Some(Vec::new()));
        assert_eq!(caps_clause(" Read, Write "), None);
    }
}
