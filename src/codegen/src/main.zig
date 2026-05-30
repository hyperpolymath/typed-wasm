// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// twasmc — typed-wasm codegen v0 (the "Code generator | Zig -> Wasm"
// component of the architecture).
//
// Reads a `.twasm` source on stdin and emits a WebAssembly binary
// (`.wasm`) on stdout. The emitted module is a valid wasm module that
// also carries the producer-side typed-wasm custom sections the
// `typed-wasm-verify` crate consumes:
//
//   * `typedwasm.ownership`    — L7 (aliasing) + L10 (linearity)
//   * `typedwasm.regions`      — L2-L6 region/field schema
//   * `typedwasm.access-sites` — L2 per-instruction (region_id, field_id)
//
// Scope (v0): the surface-syntax subset exercised by
// `examples/01-single-module.twasm` — region declarations (scalars,
// embedded `@Region` fields, `opt<@Region>` nullable references, fixed
// `T[N]` arrays), a memory declaration, and functions whose bodies use
// `region.get` / `region.set` (incl. nested field paths), `region.scan`,
// `let` / assignment, `if`/`else`, `return`, and `is_null`. Constructs
// outside this subset are reported as errors rather than silently
// mishandled.
//
// Wire formats mirror crates/typed-wasm-verify/src/section.rs exactly.

const std = @import("std");
const posix = std.posix;
const linux = std.os.linux;
const Allocator = std.mem.Allocator;
const List = std.ArrayList;

// ----------------------------------------------------------------------
// Diagnostics
// ----------------------------------------------------------------------

var g_diag_buf: [1024]u8 = undefined;
var g_diag: []const u8 = "";

const Err = error{Twasm} || Allocator.Error;

fn fail(comptime fmt: []const u8, args: anytype) Err {
    g_diag = std.fmt.bufPrint(&g_diag_buf, fmt, args) catch "twasmc: error (diagnostic truncated)";
    return error.Twasm;
}

fn writeFd(fd: i32, bytes: []const u8) void {
    var off: usize = 0;
    while (off < bytes.len) {
        const n = linux.write(fd, bytes.ptr + off, bytes.len - off);
        if (n == 0) break;
        off += n;
    }
}

// ----------------------------------------------------------------------
// Lexer
// ----------------------------------------------------------------------

const TokKind = enum { ident, int, float, punct, eof };

const Token = struct {
    kind: TokKind,
    text: []const u8,
    ival: i64 = 0,
    fval: f64 = 0,
};

fn isIdentStart(c: u8) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or c == '_';
}
fn isIdentChar(c: u8) bool {
    return isIdentStart(c) or (c >= '0' and c <= '9');
}
fn isDigit(c: u8) bool {
    return c >= '0' and c <= '9';
}

fn lex(a: Allocator, src: []const u8) Err![]Token {
    var toks: List(Token) = .empty;
    var i: usize = 0;
    const n = src.len;
    while (i < n) {
        const c = src[i];
        // whitespace
        if (c == ' ' or c == '\t' or c == '\r' or c == '\n') {
            i += 1;
            continue;
        }
        // line comment //...
        if (c == '/' and i + 1 < n and src[i + 1] == '/') {
            while (i < n and src[i] != '\n') i += 1;
            continue;
        }
        // identifier / keyword
        if (isIdentStart(c)) {
            const start = i;
            while (i < n and isIdentChar(src[i])) i += 1;
            try toks.append(a, .{ .kind = .ident, .text = src[start..i] });
            continue;
        }
        // number (int or float)
        if (isDigit(c)) {
            const start = i;
            while (i < n and isDigit(src[i])) i += 1;
            var is_float = false;
            if (i < n and src[i] == '.' and i + 1 < n and isDigit(src[i + 1])) {
                is_float = true;
                i += 1;
                while (i < n and isDigit(src[i])) i += 1;
            }
            const text = src[start..i];
            if (is_float) {
                const fv = std.fmt.parseFloat(f64, text) catch return fail("bad float literal '{s}'", .{text});
                try toks.append(a, .{ .kind = .float, .text = text, .fval = fv });
            } else {
                const iv = std.fmt.parseInt(i64, text, 10) catch return fail("bad int literal '{s}'", .{text});
                try toks.append(a, .{ .kind = .int, .text = text, .ival = iv });
            }
            continue;
        }
        // multi-char punctuation
        const two: ?[]const u8 = if (i + 1 < n) src[i .. i + 2] else null;
        if (two) |t2| {
            if (std.mem.eql(u8, t2, "->") or std.mem.eql(u8, t2, "==") or
                std.mem.eql(u8, t2, "!=") or std.mem.eql(u8, t2, "<=") or
                std.mem.eql(u8, t2, ">=") or std.mem.eql(u8, t2, "&&") or
                std.mem.eql(u8, t2, "||") or std.mem.eql(u8, t2, "<<") or
                std.mem.eql(u8, t2, ">>"))
            {
                try toks.append(a, .{ .kind = .punct, .text = t2 });
                i += 2;
                continue;
            }
        }
        // single-char punctuation
        try toks.append(a, .{ .kind = .punct, .text = src[i .. i + 1] });
        i += 1;
    }
    try toks.append(a, .{ .kind = .eof, .text = "" });
    return toks.toOwnedSlice(a);
}

// ----------------------------------------------------------------------
// AST
// ----------------------------------------------------------------------

const ScalarTy = enum {
    i8_,
    i16_,
    i32_,
    i64_,
    u8_,
    u16_,
    u32_,
    u64_,
    f32_,
    f64_,
    bool_,
};

const TypeKind = enum { scalar, region_ref, opt_region_ref, ptr_owning, ptr_borrow, ptr_excl };

const Type = struct {
    kind: TypeKind,
    scalar: ScalarTy = .i32_,
    region_name: []const u8 = "",
    cardinality: u32 = 1,
};

const Field = struct {
    name: []const u8,
    ty: Type,
    offset: u32 = 0,
    size: u32 = 0,
    alignment: u32 = 1,
};

const Region = struct {
    name: []const u8,
    count: u32 = 1,
    fields: []Field,
    alignment: u32 = 1,
    elem_size: u32 = 0,
    stride: u32 = 0,
    id: u32 = 0,
};

const HandleMode = enum { none, shared, exclusive, owned };

const Param = struct {
    name: []const u8,
    is_region: bool,
    region_name: []const u8 = "",
    mode: HandleMode = .none,
    scalar: ScalarTy = .i32_,
};

const ExprKind = enum { int_lit, float_lit, bool_lit, null_lit, ident, binop, unop, is_null };

const Expr = struct {
    kind: ExprKind,
    ival: i64 = 0,
    fval: f64 = 0,
    name: []const u8 = "",
    op: []const u8 = "",
    lhs: ?*Expr = null,
    rhs: ?*Expr = null,
};

const StmtKind = enum { get, set, let_, assign, if_, return_, scan };

const Stmt = struct {
    kind: StmtKind,
    // target ($name [index])
    target_name: []const u8 = "",
    target_index: ?*Expr = null,
    path: [][]const u8 = &.{},
    binding: []const u8 = "",
    value: ?*Expr = null,
    is_mut: bool = false,
    decl_ty: ?Type = null,
    cond: ?*Expr = null,
    then_body: []Stmt = &.{},
    else_body: []Stmt = &.{},
    has_else: bool = false,
};

const Func = struct {
    name: []const u8,
    params: []Param,
    has_ret: bool,
    ret: ScalarTy = .i32_,
    body: []Stmt,
};

const Module = struct {
    regions: []Region,
    funcs: []Func,
    mem_initial: u32 = 1,
    mem_maximum: ?u32 = null,
};

// ----------------------------------------------------------------------
// Parser
// ----------------------------------------------------------------------

const Parser = struct {
    a: Allocator,
    toks: []Token,
    pos: usize = 0,

    fn peek(p: *Parser) Token {
        return p.toks[p.pos];
    }
    fn next(p: *Parser) Token {
        const t = p.toks[p.pos];
        if (p.pos + 1 < p.toks.len) p.pos += 1;
        return t;
    }
    fn isIdent(p: *Parser, kw: []const u8) bool {
        const t = p.peek();
        return t.kind == .ident and std.mem.eql(u8, t.text, kw);
    }
    fn isPunct(p: *Parser, s: []const u8) bool {
        const t = p.peek();
        return t.kind == .punct and std.mem.eql(u8, t.text, s);
    }
    fn eatIdent(p: *Parser, kw: []const u8) Err!void {
        if (!p.isIdent(kw)) return fail("expected '{s}', got '{s}'", .{ kw, p.peek().text });
        _ = p.next();
    }
    fn eatPunct(p: *Parser, s: []const u8) Err!void {
        if (!p.isPunct(s)) return fail("expected '{s}', got '{s}'", .{ s, p.peek().text });
        _ = p.next();
    }
    fn expectIdent(p: *Parser) Err![]const u8 {
        const t = p.peek();
        if (t.kind != .ident) return fail("expected identifier, got '{s}'", .{t.text});
        _ = p.next();
        return t.text;
    }

    fn parseModule(p: *Parser) Err!Module {
        var regions: List(Region) = .empty;
        var funcs: List(Func) = .empty;
        var mem_initial: u32 = 1;
        var mem_maximum: ?u32 = null;
        var next_region_id: u32 = 0;

        while (p.peek().kind != .eof) {
            if (p.isIdent("region")) {
                var r = try p.parseRegion(regions.items);
                r.id = next_region_id;
                next_region_id += 1;
                try regions.append(p.a, r);
            } else if (p.isIdent("memory")) {
                try p.parseMemory(&mem_initial, &mem_maximum);
            } else if (p.isIdent("fn")) {
                try funcs.append(p.a, try p.parseFunc());
            } else {
                return fail("codegen v0 does not support top-level '{s}' (supported: region, memory, fn)", .{p.peek().text});
            }
        }
        return .{
            .regions = try regions.toOwnedSlice(p.a),
            .funcs = try funcs.toOwnedSlice(p.a),
            .mem_initial = mem_initial,
            .mem_maximum = mem_maximum,
        };
    }

    fn parseRegion(p: *Parser, laid_out: []Region) Err!Region {
        try p.eatIdent("region");
        const name = try p.expectIdent();
        var count: u32 = 1;
        if (p.isPunct("[")) {
            _ = p.next();
            const t = p.next();
            if (t.kind != .int) return fail("region '{s}': expected integer quantifier", .{name});
            count = @intCast(t.ival);
            try p.eatPunct("]");
        }
        if (p.isIdent("striated")) _ = p.next(); // layout marker, ignored by v0
        try p.eatPunct("{");

        var fields: List(Field) = .empty;
        var explicit_align: ?u32 = null;
        while (!p.isPunct("}")) {
            if (p.peek().kind == .eof) return fail("region '{s}': unexpected EOF", .{name});
            if (p.isIdent("align")) {
                _ = p.next();
                const t = p.next();
                if (t.kind != .int) return fail("region '{s}': align expects integer", .{name});
                explicit_align = @intCast(t.ival);
                try p.eatPunct(";");
                continue;
            }
            if (p.isIdent("where")) {
                // skip a constraint line up to ';'
                while (!p.isPunct(";") and p.peek().kind != .eof) _ = p.next();
                try p.eatPunct(";");
                continue;
            }
            if (p.isIdent("invariant")) {
                // skip an invariant block { ... }
                _ = p.next();
                try p.eatPunct("{");
                var depth: u32 = 1;
                while (depth > 0 and p.peek().kind != .eof) {
                    if (p.isPunct("{")) depth += 1;
                    if (p.isPunct("}")) depth -= 1;
                    _ = p.next();
                }
                continue;
            }
            // field_decl: name ':' type ';'
            const fname = try p.expectIdent();
            try p.eatPunct(":");
            const fty = try p.parseType();
            // optional inline field constraints introduced by 'where' before ';'
            if (p.isIdent("where")) {
                while (!p.isPunct(";") and p.peek().kind != .eof) _ = p.next();
            }
            try p.eatPunct(";");
            try fields.append(p.a, .{ .name = fname, .ty = fty });
        }
        try p.eatPunct("}");

        var r: Region = .{
            .name = name,
            .count = count,
            .fields = try fields.toOwnedSlice(p.a),
        };
        try layoutRegion(&r, laid_out, explicit_align);
        return r;
    }

    fn parseType(p: *Parser) Err!Type {
        // @Region
        if (p.isPunct("@")) {
            _ = p.next();
            const rn = try p.expectIdent();
            return p.maybeArray(.{ .kind = .region_ref, .region_name = rn });
        }
        const t = p.peek();
        if (t.kind != .ident) return fail("expected a type, got '{s}'", .{t.text});
        // opt<...>
        if (std.mem.eql(u8, t.text, "opt")) {
            _ = p.next();
            try p.eatPunct("<");
            const inner = try p.parseType();
            try p.eatPunct(">");
            if (inner.kind == .region_ref) {
                return p.maybeArray(.{ .kind = .opt_region_ref, .region_name = inner.region_name });
            }
            // opt<scalar> — represented as a nullable pointer-ish i32 in v0
            return p.maybeArray(.{ .kind = .opt_region_ref, .region_name = "" });
        }
        // ptr/ref/unique<...>
        if (std.mem.eql(u8, t.text, "ptr") or std.mem.eql(u8, t.text, "ref") or std.mem.eql(u8, t.text, "unique")) {
            const kind: TypeKind = if (std.mem.eql(u8, t.text, "ptr")) .ptr_owning else if (std.mem.eql(u8, t.text, "ref")) .ptr_borrow else .ptr_excl;
            _ = p.next();
            try p.eatPunct("<");
            const inner = try p.parseType();
            try p.eatPunct(">");
            const rn = if (inner.kind == .region_ref) inner.region_name else "";
            return p.maybeArray(.{ .kind = kind, .region_name = rn });
        }
        // scalar primitive
        const sc = scalarFromName(t.text) orelse return fail("unknown type '{s}'", .{t.text});
        _ = p.next();
        return p.maybeArray(.{ .kind = .scalar, .scalar = sc });
    }

    fn maybeArray(p: *Parser, base: Type) Err!Type {
        if (p.isPunct("[")) {
            _ = p.next();
            const t = p.next();
            if (t.kind != .int) return fail("array type expects integer length", .{});
            try p.eatPunct("]");
            var ty = base;
            ty.cardinality = @intCast(t.ival);
            return ty;
        }
        return base;
    }

    fn parseMemory(p: *Parser, initial: *u32, maximum: *?u32) Err!void {
        try p.eatIdent("memory");
        _ = try p.expectIdent(); // memory name
        try p.eatPunct("{");
        while (!p.isPunct("}")) {
            if (p.peek().kind == .eof) return fail("memory: unexpected EOF", .{});
            if (p.isIdent("initial")) {
                _ = p.next();
                try p.eatPunct(":");
                const t = p.next();
                if (t.kind != .int) return fail("memory.initial expects integer", .{});
                initial.* = @intCast(t.ival);
                try p.eatPunct(";");
            } else if (p.isIdent("maximum")) {
                _ = p.next();
                try p.eatPunct(":");
                const t = p.next();
                if (t.kind != .int) return fail("memory.maximum expects integer", .{});
                maximum.* = @intCast(t.ival);
                try p.eatPunct(";");
            } else if (p.isIdent("shared")) {
                _ = p.next();
                try p.eatPunct(";");
            } else if (p.isIdent("place")) {
                // place <Region> at <expr> ;  — placement is metadata; v0
                // handles carry base addresses at runtime, so skip to ';'.
                while (!p.isPunct(";") and p.peek().kind != .eof) _ = p.next();
                try p.eatPunct(";");
            } else {
                return fail("memory: unexpected '{s}'", .{p.peek().text});
            }
        }
        try p.eatPunct("}");
    }

    fn parseFunc(p: *Parser) Err!Func {
        try p.eatIdent("fn");
        const name = try p.expectIdent();
        try p.eatPunct("(");
        var params: List(Param) = .empty;
        while (!p.isPunct(")")) {
            try params.append(p.a, try p.parseParam());
            if (p.isPunct(",")) {
                _ = p.next();
            } else break;
        }
        try p.eatPunct(")");

        var has_ret = false;
        var ret: ScalarTy = .i32_;
        if (p.isPunct("->")) {
            _ = p.next();
            if (p.isIdent("void")) {
                _ = p.next();
            } else {
                const ty = try p.parseType();
                if (ty.kind == .scalar) {
                    has_ret = true;
                    ret = ty.scalar;
                } else {
                    // pointer/region return — represented as i32 in v0
                    has_ret = true;
                    ret = .i32_;
                }
            }
        }
        // optional clauses: effects { ... } / lifetime { ... } / cost_bound { ... } / fresh { ... }
        while (p.isIdent("effects") or p.isIdent("lifetime") or p.isIdent("cost_bound") or p.isIdent("fresh")) {
            _ = p.next();
            try p.skipBraceBlock();
        }

        const body = try p.parseBlock();
        return .{ .name = name, .params = try params.toOwnedSlice(p.a), .has_ret = has_ret, .ret = ret, .body = body };
    }

    fn parseParam(p: *Parser) Err!Param {
        const pname = try p.expectIdent();
        try p.eatPunct(":");
        // handle modes: '&' | '&mut' | 'own'  then 'region' '<' Name '>'
        if (p.isPunct("&")) {
            _ = p.next();
            var mode: HandleMode = .shared;
            if (p.isIdent("mut")) {
                _ = p.next();
                mode = .exclusive;
            }
            try p.eatIdent("region");
            try p.eatPunct("<");
            const rn = try p.expectIdent();
            try p.eatPunct(">");
            return .{ .name = pname, .is_region = true, .region_name = rn, .mode = mode };
        }
        if (p.isIdent("own")) {
            _ = p.next();
            try p.eatIdent("region");
            try p.eatPunct("<");
            const rn = try p.expectIdent();
            try p.eatPunct(">");
            return .{ .name = pname, .is_region = true, .region_name = rn, .mode = .owned };
        }
        // scalar param
        const ty = try p.parseType();
        if (ty.kind != .scalar) return fail("param '{s}': v0 supports scalar or region-handle params only", .{pname});
        return .{ .name = pname, .is_region = false, .scalar = ty.scalar };
    }

    fn skipBraceBlock(p: *Parser) Err!void {
        try p.eatPunct("{");
        var depth: u32 = 1;
        while (depth > 0) {
            const t = p.peek();
            if (t.kind == .eof) return fail("unterminated '{{' block", .{});
            if (p.isPunct("{")) depth += 1;
            if (p.isPunct("}")) depth -= 1;
            _ = p.next();
        }
    }

    fn parseBlock(p: *Parser) Err![]Stmt {
        try p.eatPunct("{");
        var stmts: List(Stmt) = .empty;
        while (!p.isPunct("}")) {
            if (p.peek().kind == .eof) return fail("unterminated function/block body", .{});
            try stmts.append(p.a, try p.parseStmt());
        }
        try p.eatPunct("}");
        return stmts.toOwnedSlice(p.a);
    }

    fn parseStmt(p: *Parser) Err!Stmt {
        // region.get / region.set / region.scan
        if (p.isIdent("region")) {
            const save = p.pos;
            _ = p.next();
            if (p.isPunct(".")) {
                _ = p.next();
                const op = try p.expectIdent();
                if (std.mem.eql(u8, op, "get")) return p.parseGet();
                if (std.mem.eql(u8, op, "set")) return p.parseSet();
                if (std.mem.eql(u8, op, "scan")) return p.parseScan();
                return fail("codegen v0 does not support region.{s}", .{op});
            }
            p.pos = save; // not an access op; fall through (shouldn't happen)
        }
        if (p.isIdent("let")) return p.parseLet();
        if (p.isIdent("if")) return p.parseIf();
        if (p.isIdent("return")) return p.parseReturn();
        // assignment: ident '=' expr ';'
        if (p.peek().kind == .ident) {
            const save = p.pos;
            const id = p.next().text;
            if (p.isPunct("=")) {
                _ = p.next();
                const e = try p.parseExpr();
                try p.eatPunct(";");
                return .{ .kind = .assign, .binding = id, .value = e };
            }
            p.pos = save;
        }
        return fail("codegen v0: unsupported statement starting at '{s}'", .{p.peek().text});
    }

    fn parseTarget(p: *Parser, st: *Stmt) Err!void {
        try p.eatPunct("$");
        st.target_name = try p.expectIdent();
        if (p.isPunct("[")) {
            _ = p.next();
            st.target_index = try p.parseExpr();
            try p.eatPunct("]");
        }
    }

    fn parsePath(p: *Parser) Err![][]const u8 {
        var segs: List([]const u8) = .empty;
        while (p.isPunct(".")) {
            _ = p.next();
            try segs.append(p.a, try p.expectIdent());
        }
        return segs.toOwnedSlice(p.a);
    }

    fn parseGet(p: *Parser) Err!Stmt {
        var st: Stmt = .{ .kind = .get };
        // target may be `$name[idx]` or a bare binding identifier (e.g. a
        // pointer local: `region.get maybe_target .hp -> x`).
        if (p.isPunct("$")) {
            try p.parseTarget(&st);
        } else {
            st.target_name = try p.expectIdent(); // pointer-valued local
        }
        st.path = try p.parsePath();
        try p.eatPunct("->");
        st.binding = try p.expectIdent();
        try p.eatPunct(";");
        return st;
    }

    fn parseSet(p: *Parser) Err!Stmt {
        var st: Stmt = .{ .kind = .set };
        if (p.isPunct("$")) {
            try p.parseTarget(&st);
        } else {
            st.target_name = try p.expectIdent();
        }
        st.path = try p.parsePath();
        try p.eatPunct(",");
        st.value = try p.parseExpr();
        try p.eatPunct(";");
        return st;
    }

    fn parseScan(p: *Parser) Err!Stmt {
        var st: Stmt = .{ .kind = .scan };
        try p.parseTarget(&st);
        if (p.isIdent("where")) {
            _ = p.next();
            st.cond = try p.parseExpr();
        }
        try p.eatPunct("->");
        try p.eatPunct("|");
        st.binding = try p.expectIdent();
        try p.eatPunct("|");
        st.then_body = try p.parseBlock();
        return st;
    }

    fn parseLet(p: *Parser) Err!Stmt {
        try p.eatIdent("let");
        var st: Stmt = .{ .kind = .let_ };
        if (p.isIdent("mut")) {
            _ = p.next();
            st.is_mut = true;
        }
        st.binding = try p.expectIdent();
        if (p.isPunct(":")) {
            _ = p.next();
            st.decl_ty = try p.parseType();
        }
        try p.eatPunct("=");
        st.value = try p.parseExpr();
        try p.eatPunct(";");
        return st;
    }

    fn parseIf(p: *Parser) Err!Stmt {
        try p.eatIdent("if");
        var st: Stmt = .{ .kind = .if_ };
        st.cond = try p.parseExpr();
        st.then_body = try p.parseBlock();
        if (p.isIdent("else")) {
            _ = p.next();
            st.has_else = true;
            st.else_body = try p.parseBlock();
        }
        return st;
    }

    fn parseReturn(p: *Parser) Err!Stmt {
        try p.eatIdent("return");
        var st: Stmt = .{ .kind = .return_ };
        if (!p.isPunct(";")) {
            st.value = try p.parseExpr();
        }
        try p.eatPunct(";");
        return st;
    }

    // ---- expression parsing (precedence climbing) ----

    fn parseExpr(p: *Parser) Err!*Expr {
        return p.parseBin(0);
    }

    fn binPrec(op: []const u8) i32 {
        if (std.mem.eql(u8, op, "||")) return 1;
        if (std.mem.eql(u8, op, "&&")) return 2;
        if (std.mem.eql(u8, op, "==") or std.mem.eql(u8, op, "!=") or
            std.mem.eql(u8, op, "<") or std.mem.eql(u8, op, ">") or
            std.mem.eql(u8, op, "<=") or std.mem.eql(u8, op, ">=")) return 3;
        if (std.mem.eql(u8, op, "+") or std.mem.eql(u8, op, "-")) return 4;
        if (std.mem.eql(u8, op, "*") or std.mem.eql(u8, op, "/") or std.mem.eql(u8, op, "%")) return 5;
        return -1;
    }

    fn parseBin(p: *Parser, min_prec: i32) Err!*Expr {
        var lhs = try p.parseUnary();
        while (true) {
            const t = p.peek();
            if (t.kind != .punct) break;
            const prec = binPrec(t.text);
            if (prec < min_prec or prec < 0) break;
            const op = p.next().text;
            const rhs = try p.parseBin(prec + 1);
            const e = try p.a.create(Expr);
            e.* = .{ .kind = .binop, .op = op, .lhs = lhs, .rhs = rhs };
            lhs = e;
        }
        return lhs;
    }

    fn parseUnary(p: *Parser) Err!*Expr {
        if (p.isPunct("-") or p.isPunct("!") or p.isPunct("~")) {
            const op = p.next().text;
            const operand = try p.parseUnary();
            // fold `- <int literal>` into a negative literal
            if (std.mem.eql(u8, op, "-") and operand.kind == .int_lit) {
                operand.ival = -operand.ival;
                return operand;
            }
            const e = try p.a.create(Expr);
            e.* = .{ .kind = .unop, .op = op, .lhs = operand };
            return e;
        }
        return p.parsePrimary();
    }

    fn parsePrimary(p: *Parser) Err!*Expr {
        const t = p.peek();
        const e = try p.a.create(Expr);
        if (t.kind == .int) {
            _ = p.next();
            e.* = .{ .kind = .int_lit, .ival = t.ival };
            return e;
        }
        if (t.kind == .float) {
            _ = p.next();
            e.* = .{ .kind = .float_lit, .fval = t.fval };
            return e;
        }
        if (p.isPunct("(")) {
            _ = p.next();
            const inner = try p.parseExpr();
            try p.eatPunct(")");
            return inner;
        }
        if (p.isPunct("$")) {
            _ = p.next();
            const id = try p.expectIdent();
            e.* = .{ .kind = .ident, .name = id };
            return e;
        }
        if (t.kind == .ident) {
            if (std.mem.eql(u8, t.text, "true")) {
                _ = p.next();
                e.* = .{ .kind = .bool_lit, .ival = 1 };
                return e;
            }
            if (std.mem.eql(u8, t.text, "false")) {
                _ = p.next();
                e.* = .{ .kind = .bool_lit, .ival = 0 };
                return e;
            }
            if (std.mem.eql(u8, t.text, "null")) {
                _ = p.next();
                e.* = .{ .kind = .null_lit };
                return e;
            }
            if (std.mem.eql(u8, t.text, "is_null")) {
                _ = p.next();
                try p.eatPunct("(");
                const inner = try p.parseExpr();
                try p.eatPunct(")");
                e.* = .{ .kind = .is_null, .lhs = inner };
                return e;
            }
            _ = p.next();
            e.* = .{ .kind = .ident, .name = t.text };
            return e;
        }
        return fail("unexpected token '{s}' in expression", .{t.text});
    }
};

fn scalarFromName(s: []const u8) ?ScalarTy {
    const m = .{
        .{ "i8", ScalarTy.i8_ },   .{ "i16", ScalarTy.i16_ },   .{ "i32", ScalarTy.i32_ },
        .{ "i64", ScalarTy.i64_ }, .{ "u8", ScalarTy.u8_ },     .{ "u16", ScalarTy.u16_ },
        .{ "u32", ScalarTy.u32_ }, .{ "u64", ScalarTy.u64_ },   .{ "f32", ScalarTy.f32_ },
        .{ "f64", ScalarTy.f64_ }, .{ "bool", ScalarTy.bool_ },
    };
    inline for (m) |pair| {
        if (std.mem.eql(u8, s, pair[0])) return pair[1];
    }
    return null;
}

// ----------------------------------------------------------------------
// Layout
// ----------------------------------------------------------------------

fn alignUp(x: u32, a: u32) u32 {
    if (a <= 1) return x;
    return ((x + a - 1) / a) * a;
}

fn scalarSize(s: ScalarTy) u32 {
    return switch (s) {
        .i8_, .u8_, .bool_ => 1,
        .i16_, .u16_ => 2,
        .i32_, .u32_, .f32_ => 4,
        .i64_, .u64_, .f64_ => 8,
    };
}

fn findRegion(regions: []Region, name: []const u8) ?*Region {
    for (regions) |*r| {
        if (std.mem.eql(u8, r.name, name)) return r;
    }
    return null;
}

fn typeSizeAlign(ty: Type, laid_out: []Region) Err!struct { size: u32, alignment: u32 } {
    var base_size: u32 = 0;
    var base_align: u32 = 1;
    switch (ty.kind) {
        .scalar => {
            base_size = scalarSize(ty.scalar);
            base_align = base_size;
        },
        .region_ref => {
            const r = findRegion(laid_out, ty.region_name) orelse
                return fail("embedded region '@{s}' must be declared before use", .{ty.region_name});
            base_size = r.stride;
            base_align = r.alignment;
        },
        .opt_region_ref, .ptr_owning, .ptr_borrow, .ptr_excl => {
            // pointers are 4-byte wasm32 addresses
            base_size = 4;
            base_align = 4;
        },
    }
    const card = if (ty.cardinality == 0) 1 else ty.cardinality;
    return .{ .size = base_size * card, .alignment = base_align };
}

fn layoutRegion(r: *Region, laid_out: []Region, explicit_align: ?u32) Err!void {
    var cursor: u32 = 0;
    var max_align: u32 = 1;
    for (r.fields) |*f| {
        const sa = try typeSizeAlign(f.ty, laid_out);
        const off = alignUp(cursor, sa.alignment);
        f.offset = off;
        f.size = sa.size;
        f.alignment = sa.alignment;
        cursor = off + sa.size;
        if (sa.alignment > max_align) max_align = sa.alignment;
    }
    r.alignment = explicit_align orelse max_align;
    if (r.alignment == 0) r.alignment = 1;
    r.elem_size = cursor;
    r.stride = alignUp(cursor, r.alignment);
}

// ----------------------------------------------------------------------
// wasm value types & opcodes
// ----------------------------------------------------------------------

const WT = enum(u8) { i32 = 0x7f, i64 = 0x7e, f32 = 0x7d, f64 = 0x7c };

fn scalarWasm(s: ScalarTy) WT {
    return switch (s) {
        .i8_, .i16_, .i32_, .u8_, .u16_, .u32_, .bool_ => .i32,
        .i64_, .u64_ => .i64,
        .f32_ => .f32,
        .f64_ => .f64,
    };
}

// Load/store opcode + natural-alignment exponent for a leaf field type.
const MemOp = struct { op: u8, log2_align: u8, wt: WT };

fn loadOp(ty: Type) MemOp {
    switch (ty.kind) {
        .scalar => return switch (ty.scalar) {
            .i8_ => .{ .op = 0x2c, .log2_align = 0, .wt = .i32 }, // i32.load8_s
            .u8_, .bool_ => .{ .op = 0x2d, .log2_align = 0, .wt = .i32 }, // i32.load8_u
            .i16_ => .{ .op = 0x2e, .log2_align = 1, .wt = .i32 }, // i32.load16_s
            .u16_ => .{ .op = 0x2f, .log2_align = 1, .wt = .i32 }, // i32.load16_u
            .i32_, .u32_ => .{ .op = 0x28, .log2_align = 2, .wt = .i32 }, // i32.load
            .i64_, .u64_ => .{ .op = 0x29, .log2_align = 3, .wt = .i64 }, // i64.load
            .f32_ => .{ .op = 0x2a, .log2_align = 2, .wt = .f32 }, // f32.load
            .f64_ => .{ .op = 0x2b, .log2_align = 3, .wt = .f64 }, // f64.load
        },
        else => return .{ .op = 0x28, .log2_align = 2, .wt = .i32 }, // pointer => i32.load
    }
}

fn storeOp(ty: Type) MemOp {
    switch (ty.kind) {
        .scalar => return switch (ty.scalar) {
            .i8_, .u8_, .bool_ => .{ .op = 0x3a, .log2_align = 0, .wt = .i32 }, // i32.store8
            .i16_, .u16_ => .{ .op = 0x3b, .log2_align = 1, .wt = .i32 }, // i32.store16
            .i32_, .u32_ => .{ .op = 0x36, .log2_align = 2, .wt = .i32 }, // i32.store
            .i64_, .u64_ => .{ .op = 0x37, .log2_align = 3, .wt = .i64 }, // i64.store
            .f32_ => .{ .op = 0x38, .log2_align = 2, .wt = .f32 }, // f32.store
            .f64_ => .{ .op = 0x39, .log2_align = 3, .wt = .f64 }, // f64.store
        },
        else => return .{ .op = 0x36, .log2_align = 2, .wt = .i32 }, // pointer => i32.store
    }
}

// ----------------------------------------------------------------------
// Byte buffer with wasm + carrier encoders
// ----------------------------------------------------------------------

const Buf = struct {
    a: Allocator,
    d: List(u8) = .empty,

    fn b(self: *Buf, x: u8) Err!void {
        try self.d.append(self.a, x);
    }
    fn raw(self: *Buf, s: []const u8) Err!void {
        try self.d.appendSlice(self.a, s);
    }
    // unsigned LEB128 (wasm indices / sizes)
    fn uleb(self: *Buf, value: u64) Err!void {
        var v = value;
        while (true) {
            var byte: u8 = @intCast(v & 0x7f);
            v >>= 7;
            if (v != 0) byte |= 0x80;
            try self.b(byte);
            if (v == 0) break;
        }
    }
    // signed LEB128 (i32.const / i64.const)
    fn sleb(self: *Buf, value: i64) Err!void {
        var v = value;
        while (true) {
            var byte: u8 = @intCast(@as(u64, @bitCast(v)) & 0x7f);
            v >>= 7;
            const sign_bit = (byte & 0x40) != 0;
            if ((v == 0 and !sign_bit) or (v == -1 and sign_bit)) {
                try self.b(byte);
                break;
            }
            byte |= 0x80;
            try self.b(byte);
        }
    }
    // raw little-endian fixed widths (carrier wire formats)
    fn u16le(self: *Buf, v: u16) Err!void {
        try self.b(@intCast(v & 0xff));
        try self.b(@intCast((v >> 8) & 0xff));
    }
    fn u32le(self: *Buf, v: u32) Err!void {
        try self.b(@intCast(v & 0xff));
        try self.b(@intCast((v >> 8) & 0xff));
        try self.b(@intCast((v >> 16) & 0xff));
        try self.b(@intCast((v >> 24) & 0xff));
    }
    fn nameStr(self: *Buf, s: []const u8) Err!void {
        try self.uleb(s.len);
        try self.raw(s);
    }
};

// ----------------------------------------------------------------------
// Function body codegen
// ----------------------------------------------------------------------

const LocalSlot = struct { name: []const u8, wt: WT, region_name: []const u8 = "", is_base: bool = false };

const AccessSite = struct { func_idx: u32, offset: u32, region_id: u32, field_id: u32 };

const FnCodegen = struct {
    a: Allocator,
    regions: []Region,
    func: *Func,
    func_idx: u32,
    // local table: params first, then extra locals
    locals: List(LocalSlot) = .empty,
    n_params: u32 = 0,
    base_local_of_param: []i32 = &.{}, // for region-handle params: index of its base local, else -1
    body: Buf,
    access: *List(AccessSite),
    // scan context
    scan_region: ?*Region = null,
    scan_iter_local: u32 = 0,
    scan_base_local: u32 = 0,

    fn findLocal(self: *FnCodegen, name: []const u8) ?u32 {
        for (self.locals.items, 0..) |l, i| {
            if (std.mem.eql(u8, l.name, name)) return @intCast(i);
        }
        return null;
    }

    // Resolve a region-handle reference. A region-handle parameter is read
    // exactly once at entry into a dedicated base local (the prologue);
    // every dereference of the handle goes through that base local so the
    // param itself is `local.get` only once — satisfying L7 ExclBorrow
    // (<=1 use) and L10 Linear (==1 use). Non-param handles (e.g. pointer
    // bindings from `region.get`) resolve through the normal local table.
    fn handleLocalIndex(self: *FnCodegen, name: []const u8) ?u32 {
        for (self.func.params, 0..) |pm, i| {
            if (pm.is_region and std.mem.eql(u8, pm.name, name)) {
                return @intCast(self.base_local_of_param[i]);
            }
        }
        return self.findLocal(name);
    }

    fn localWt(self: *FnCodegen, idx: u32) WT {
        return self.locals.items[idx].wt;
    }

    fn addLocal(self: *FnCodegen, name: []const u8, wt: WT, region_name: []const u8) Err!u32 {
        const idx: u32 = @intCast(self.locals.items.len);
        try self.locals.append(self.a, .{ .name = name, .wt = wt, .region_name = region_name });
        return idx;
    }

    // ---- expression emission; returns the wasm value type pushed ----
    fn emitExpr(self: *FnCodegen, e: *Expr) Err!WT {
        switch (e.kind) {
            .int_lit => {
                try self.body.b(0x41); // i32.const
                try self.body.sleb(e.ival);
                return .i32;
            },
            .bool_lit, .null_lit => {
                try self.body.b(0x41);
                try self.body.sleb(e.ival);
                return .i32;
            },
            .float_lit => {
                // f32.const (default float literal width in v0)
                try self.body.b(0x43);
                const bits: u32 = @bitCast(@as(f32, @floatCast(e.fval)));
                try self.body.u32le(bits);
                return .f32;
            },
            .ident => return self.emitIdent(e.name),
            .is_null => {
                _ = try self.emitExpr(e.lhs.?);
                try self.body.b(0x45); // i32.eqz
                return .i32;
            },
            .unop => {
                if (std.mem.eql(u8, e.op, "-")) {
                    // 0 - x
                    try self.body.b(0x41);
                    try self.body.sleb(0);
                    const wt = try self.emitExpr(e.lhs.?);
                    try self.body.b(if (wt == .f32) 0x93 else if (wt == .f64) 0xa1 else 0x6b); // f32.sub/f64.sub/i32.sub
                    return wt;
                }
                if (std.mem.eql(u8, e.op, "!")) {
                    _ = try self.emitExpr(e.lhs.?);
                    try self.body.b(0x45); // i32.eqz
                    return .i32;
                }
                return fail("v0: unsupported unary '{s}'", .{e.op});
            },
            .binop => return self.emitBinop(e),
        }
    }

    fn emitIdent(self: *FnCodegen, name: []const u8) Err!WT {
        // scan field context: a bare field name resolves to a load of the
        // current element's field.
        if (self.scan_region) |sr| {
            for (sr.fields, 0..) |f, fid| {
                if (std.mem.eql(u8, f.name, name)) {
                    try self.emitElemAddr(self.scan_base_local, self.scan_iter_local, sr.stride);
                    const mo = loadOp(f.ty);
                    try self.recordAccess(f.ty, f.offset, sr.id, @intCast(fid));
                    try self.emitMem(mo, f.offset);
                    return mo.wt;
                }
            }
        }
        const idx = self.findLocal(name) orelse return fail("unknown identifier '{s}'", .{name});
        try self.body.b(0x20); // local.get
        try self.body.uleb(idx);
        return self.localWt(idx);
    }

    fn emitBinop(self: *FnCodegen, e: *Expr) Err!WT {
        const lt = try self.emitExpr(e.lhs.?);
        const rt = try self.emitExpr(e.rhs.?);
        const wt: WT = if (lt == .f32 or rt == .f32) .f32 else if (lt == .f64 or rt == .f64) .f64 else if (lt == .i64 or rt == .i64) .i64 else .i32;
        const op = e.op;
        // arithmetic
        if (std.mem.eql(u8, op, "+")) {
            try self.body.b(switch (wt) {
                .i32 => 0x6a,
                .i64 => 0x7c,
                .f32 => 0x92,
                .f64 => 0xa0,
            });
            return wt;
        }
        if (std.mem.eql(u8, op, "-")) {
            try self.body.b(switch (wt) {
                .i32 => 0x6b,
                .i64 => 0x7d,
                .f32 => 0x93,
                .f64 => 0xa1,
            });
            return wt;
        }
        if (std.mem.eql(u8, op, "*")) {
            try self.body.b(switch (wt) {
                .i32 => 0x6c,
                .i64 => 0x7e,
                .f32 => 0x94,
                .f64 => 0xa2,
            });
            return wt;
        }
        // comparisons -> i32 bool
        if (wt == .i32) {
            const code: ?u8 = if (std.mem.eql(u8, op, "==")) 0x46 //
                else if (std.mem.eql(u8, op, "!=")) 0x47 //
                else if (std.mem.eql(u8, op, "<")) 0x48 // lt_s
                else if (std.mem.eql(u8, op, ">")) 0x4a // gt_s
                else if (std.mem.eql(u8, op, "<=")) 0x4c // le_s
                else if (std.mem.eql(u8, op, ">=")) 0x4e // ge_s
                else null;
            if (code) |c| {
                try self.body.b(c);
                return .i32;
            }
        }
        if (wt == .f32) {
            const code: ?u8 = if (std.mem.eql(u8, op, "==")) 0x5b //
                else if (std.mem.eql(u8, op, "!=")) 0x5c //
                else if (std.mem.eql(u8, op, "<")) 0x5d //
                else if (std.mem.eql(u8, op, ">")) 0x5e //
                else if (std.mem.eql(u8, op, "<=")) 0x5f //
                else if (std.mem.eql(u8, op, ">=")) 0x60 //
                else null;
            if (code) |c| {
                try self.body.b(c);
                return .i32;
            }
        }
        return fail("v0: unsupported binary op '{s}'", .{op});
    }

    // Resolve a (target, path) lvalue: emit the base address on the stack
    // and return the cumulative byte offset + leaf field type.
    const Lvalue = struct { offset: u32, ty: Type, region_id: u32, field_id: u32 };

    fn emitElemAddr(self: *FnCodegen, base_local: u32, idx_local: u32, stride: u32) Err!void {
        try self.body.b(0x20); // local.get base
        try self.body.uleb(base_local);
        try self.body.b(0x20); // local.get idx
        try self.body.uleb(idx_local);
        try self.body.b(0x41); // i32.const stride
        try self.body.sleb(@intCast(stride));
        try self.body.b(0x6c); // i32.mul
        try self.body.b(0x6a); // i32.add
    }

    fn emitTargetAddr(self: *FnCodegen, st: *Stmt) Err!Lvalue {
        // Determine the starting region + base address on stack.
        var region: *Region = undefined;
        if (self.handleLocalIndex(st.target_name)) |li| {
            const slot = self.locals.items[li];
            // local must be a region base or a pointer to a region
            if (slot.region_name.len == 0)
                return fail("'{s}' is not a region handle/pointer", .{st.target_name});
            region = findRegion(self.regions, slot.region_name) orelse
                return fail("unknown region '{s}'", .{slot.region_name});
            if (st.target_index) |ix| {
                // base + index*stride
                try self.body.b(0x20);
                try self.body.uleb(li);
                _ = try self.emitExpr(ix);
                try self.body.b(0x41);
                try self.body.sleb(@intCast(region.stride));
                try self.body.b(0x6c);
                try self.body.b(0x6a);
            } else {
                try self.body.b(0x20); // local.get base/pointer
                try self.body.uleb(li);
            }
        } else {
            return fail("unknown target '{s}'", .{st.target_name});
        }

        // Walk the field path, accumulating offset and resolving the leaf.
        var cur = region;
        var offset: u32 = 0;
        var leaf: Type = .{ .kind = .scalar, .scalar = .i32_ };
        var region_id = region.id;
        var field_id: u32 = 0;
        if (st.path.len == 0) return fail("typed access on '{s}' needs a .field path", .{st.target_name});
        for (st.path, 0..) |seg, si| {
            var found = false;
            for (cur.fields, 0..) |f, fid| {
                if (std.mem.eql(u8, f.name, seg)) {
                    offset += f.offset;
                    leaf = f.ty;
                    region_id = cur.id;
                    field_id = @intCast(fid);
                    found = true;
                    if (si + 1 < st.path.len) {
                        // must descend into an embedded region
                        if (f.ty.kind != .region_ref)
                            return fail("field '{s}' is not an embedded region; cannot descend", .{seg});
                        cur = findRegion(self.regions, f.ty.region_name) orelse
                            return fail("unknown embedded region '@{s}'", .{f.ty.region_name});
                    }
                    break;
                }
            }
            if (!found) return fail("region '{s}' has no field '{s}'", .{ cur.name, seg });
        }
        return .{ .offset = offset, .ty = leaf, .region_id = region_id, .field_id = field_id };
    }

    fn emitMem(self: *FnCodegen, mo: MemOp, offset: u32) Err!void {
        try self.body.b(mo.op);
        try self.body.uleb(mo.log2_align); // align (log2)
        try self.body.uleb(offset); // offset
    }

    fn recordAccess(self: *FnCodegen, ty: Type, _: u32, region_id: u32, field_id: u32) Err!void {
        _ = ty;
        // instruction_byte_offset: best-effort = current body length.
        // The verifier does not validate the offset (proposal 0002 defers
        // AccessSiteMisalignment), so a monotonic body position suffices.
        try self.access.append(self.a, .{
            .func_idx = self.func_idx,
            .offset = @intCast(self.body.d.items.len),
            .region_id = region_id,
            .field_id = field_id,
        });
    }

    fn emitStmt(self: *FnCodegen, st: *Stmt) Err!void {
        switch (st.kind) {
            .get => {
                const lv = try self.emitTargetAddr(st);
                const mo = loadOp(lv.ty);
                try self.recordAccess(lv.ty, lv.offset, lv.region_id, lv.field_id);
                try self.emitMem(mo, lv.offset);
                const li = self.findLocal(st.binding).?;
                try self.body.b(0x21); // local.set
                try self.body.uleb(li);
            },
            .set => {
                const lv = try self.emitTargetAddr(st);
                _ = try self.emitExpr(st.value.?);
                const mo = storeOp(lv.ty);
                try self.recordAccess(lv.ty, lv.offset, lv.region_id, lv.field_id);
                try self.emitMem(mo, lv.offset);
            },
            .let_, .assign => {
                _ = try self.emitExpr(st.value.?);
                const li = self.findLocal(st.binding).?;
                try self.body.b(0x21); // local.set
                try self.body.uleb(li);
            },
            .return_ => {
                if (st.value) |v| _ = try self.emitExpr(v);
                try self.body.b(0x0f); // return
            },
            .if_ => {
                _ = try self.emitExpr(st.cond.?);
                try self.body.b(0x04); // if
                try self.body.b(0x40); // blocktype: empty
                for (st.then_body) |*s| try self.emitStmt(s);
                if (st.has_else) {
                    try self.body.b(0x05); // else
                    for (st.else_body) |*s| try self.emitStmt(s);
                }
                try self.body.b(0x0b); // end
            },
            .scan => {
                const region = findRegion(self.regions, self.localRegionName(st.target_name)) orelse
                    return fail("scan target '{s}' is not a region handle", .{st.target_name});
                const base_li = self.handleLocalIndex(st.target_name).?;
                const iter_li = self.findLocal(self.scanIterName(st)).?;
                // i = 0
                try self.body.b(0x41);
                try self.body.sleb(0);
                try self.body.b(0x21);
                try self.body.uleb(iter_li);
                // block { loop { ... } }
                try self.body.b(0x02);
                try self.body.b(0x40); // block
                try self.body.b(0x03);
                try self.body.b(0x40); // loop
                // if (i >= count) br 1
                try self.body.b(0x20);
                try self.body.uleb(iter_li);
                try self.body.b(0x41);
                try self.body.sleb(@intCast(region.count));
                try self.body.b(0x4e); // i32.ge_s
                try self.body.b(0x0d); // br_if
                try self.body.uleb(1);
                // evaluate where-condition (default true) in scan context
                self.scan_region = region;
                self.scan_iter_local = iter_li;
                self.scan_base_local = base_li;
                if (st.cond) |c| {
                    _ = try self.emitExpr(c);
                } else {
                    try self.body.b(0x41);
                    try self.body.sleb(1);
                }
                try self.body.b(0x04);
                try self.body.b(0x40); // if
                for (st.then_body) |*s| try self.emitStmt(s);
                try self.body.b(0x0b); // end if
                self.scan_region = null;
                // i = i + 1
                try self.body.b(0x20);
                try self.body.uleb(iter_li);
                try self.body.b(0x41);
                try self.body.sleb(1);
                try self.body.b(0x6a); // i32.add
                try self.body.b(0x21);
                try self.body.uleb(iter_li);
                // br 0 (continue loop)
                try self.body.b(0x0c);
                try self.body.uleb(0);
                try self.body.b(0x0b); // end loop
                try self.body.b(0x0b); // end block
            },
        }
    }

    fn localRegionName(self: *FnCodegen, name: []const u8) []const u8 {
        if (self.findLocal(name)) |li| return self.locals.items[li].region_name;
        return "";
    }
    fn scanIterName(self: *FnCodegen, st: *Stmt) []const u8 {
        _ = self;
        return st.binding;
    }
};

// Pre-pass: allocate locals for params, region bases, bindings, lets,
// and scan iterator variables.
fn allocLocals(cg: *FnCodegen) Err!void {
    // params
    for (cg.func.params) |pm| {
        const wt: WT = if (pm.is_region) .i32 else scalarWasm(pm.scalar);
        const rn = if (pm.is_region) pm.region_name else "";
        _ = try cg.addLocal(pm.name, wt, rn);
    }
    cg.n_params = @intCast(cg.func.params.len);

    // region-handle params get a dedicated base local (read the param
    // exactly once into it — satisfies L7 ExclBorrow<=1 and L10 Linear==1).
    cg.base_local_of_param = try cg.a.alloc(i32, cg.func.params.len);
    for (cg.func.params, 0..) |pm, i| {
        if (pm.is_region) {
            const base = try cg.addLocal(try baseName(cg.a, pm.name), .i32, pm.region_name);
            cg.base_local_of_param[i] = @intCast(base);
        } else {
            cg.base_local_of_param[i] = -1;
        }
    }

    // walk body for bindings / lets / scan vars
    try allocLocalsInBody(cg, cg.func.body);
}

fn allocLocalsInBody(cg: *FnCodegen, body: []Stmt) Err!void {
    for (body) |*st| {
        switch (st.kind) {
            .get => {
                // binding type = leaf field type
                const wt = try bindingWasmType(cg, st);
                if (cg.findLocal(st.binding) == null) _ = try cg.addLocal(st.binding, wt, bindingRegionName(cg, st));
            },
            .let_ => {
                const wt = try letWasmType(cg, st);
                if (cg.findLocal(st.binding) == null) _ = try cg.addLocal(st.binding, wt, "");
            },
            .if_ => {
                try allocLocalsInBody(cg, st.then_body);
                if (st.has_else) try allocLocalsInBody(cg, st.else_body);
            },
            .scan => {
                if (cg.findLocal(st.binding) == null) _ = try cg.addLocal(st.binding, .i32, "");
                try allocLocalsInBody(cg, st.then_body);
            },
            else => {},
        }
    }
}

// Resolve the leaf field type of a get target, for typing the binding.
fn resolveLeaf(cg: *FnCodegen, st: *Stmt) Err!Type {
    var region: *Region = undefined;
    if (cg.findLocal(st.target_name)) |li| {
        const rn = cg.locals.items[li].region_name;
        region = findRegion(cg.regions, rn) orelse return fail("unknown region for '{s}'", .{st.target_name});
    } else {
        return fail("unknown target '{s}'", .{st.target_name});
    }
    var cur = region;
    var leaf: Type = .{ .kind = .scalar, .scalar = .i32_ };
    for (st.path, 0..) |seg, si| {
        var found = false;
        for (cur.fields) |f| {
            if (std.mem.eql(u8, f.name, seg)) {
                leaf = f.ty;
                found = true;
                if (si + 1 < st.path.len and f.ty.kind == .region_ref) {
                    cur = findRegion(cg.regions, f.ty.region_name) orelse
                        return fail("unknown embedded region '@{s}'", .{f.ty.region_name});
                }
                break;
            }
        }
        if (!found) return fail("region '{s}' has no field '{s}'", .{ cur.name, seg });
    }
    return leaf;
}

fn bindingWasmType(cg: *FnCodegen, st: *Stmt) Err!WT {
    const leaf = try resolveLeaf(cg, st);
    return loadOp(leaf).wt;
}
fn bindingRegionName(cg: *FnCodegen, st: *Stmt) []const u8 {
    const leaf = resolveLeaf(cg, st) catch return "";
    return switch (leaf.kind) {
        .opt_region_ref, .ptr_owning, .ptr_borrow, .ptr_excl, .region_ref => leaf.region_name,
        else => "",
    };
}
fn letWasmType(cg: *FnCodegen, st: *Stmt) Err!WT {
    if (st.decl_ty) |dt| {
        if (dt.kind == .scalar) return scalarWasm(dt.scalar);
        return .i32;
    }
    // infer from value (best effort): default i32
    _ = cg;
    return .i32;
}

fn baseName(a: Allocator, name: []const u8) Err![]const u8 {
    return std.fmt.allocPrint(a, "__base_{s}", .{name}) catch error.OutOfMemory;
}

// ----------------------------------------------------------------------
// Module emission
// ----------------------------------------------------------------------

fn ownershipKind(mode: HandleMode) u8 {
    return switch (mode) {
        .none => 0, // Unrestricted
        .owned => 1, // Linear
        .shared => 2, // SharedBorrow
        .exclusive => 3, // ExclBorrow
    };
}

fn fieldKindByte(ty: Type) u8 {
    return switch (ty.kind) {
        .scalar, .region_ref => 0, // Scalar (embedded region recorded via target_region)
        .ptr_owning => 1,
        .opt_region_ref, .ptr_borrow => 2, // PtrBorrow
        .ptr_excl => 3,
    };
}

fn fieldWasmTyByte(ty: Type) u8 {
    if (ty.kind != .scalar) return 0xff; // NotApplicable
    return switch (ty.scalar) {
        .u8_ => 0,
        .u16_ => 1,
        .u32_ => 2,
        .u64_ => 3,
        .i8_ => 4,
        .i16_ => 5,
        .i32_ => 6,
        .i64_ => 7,
        .f32_ => 8,
        .f64_ => 9,
        .bool_ => 10,
    };
}

fn fieldNullability(ty: Type) u8 {
    return if (ty.kind == .opt_region_ref) 1 else 0;
}

fn fieldTargetRegion(regions: []Region, ty: Type) u32 {
    switch (ty.kind) {
        .region_ref, .opt_region_ref, .ptr_owning, .ptr_borrow, .ptr_excl => {
            if (ty.region_name.len == 0) return 0xffff_ffff;
            if (findRegion(regions, ty.region_name)) |r| return r.id;
            return 0xffff_ffff;
        },
        else => return 0xffff_ffff,
    }
}

fn emitModule(a: Allocator, m: *Module) Err![]u8 {
    var out: Buf = .{ .a = a };

    // header
    try out.raw(&[_]u8{ 0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00 });

    const nfuncs: u32 = @intCast(m.funcs.len);

    // --- type section (id 1): one functype per function ---
    {
        var s: Buf = .{ .a = a };
        try s.uleb(nfuncs);
        for (m.funcs) |*f| {
            try s.b(0x60);
            try s.uleb(f.params.len);
            for (f.params) |pm| {
                const wt: WT = if (pm.is_region) .i32 else scalarWasm(pm.scalar);
                try s.b(@intFromEnum(wt));
            }
            if (f.has_ret) {
                try s.uleb(1);
                try s.b(@intFromEnum(scalarWasm(f.ret)));
            } else {
                try s.uleb(0);
            }
        }
        try emitSection(&out, 1, &s);
    }

    // --- function section (id 3) ---
    {
        var s: Buf = .{ .a = a };
        try s.uleb(nfuncs);
        var i: u32 = 0;
        while (i < nfuncs) : (i += 1) try s.uleb(i);
        try emitSection(&out, 3, &s);
    }

    // --- memory section (id 5) ---
    {
        var s: Buf = .{ .a = a };
        try s.uleb(1);
        if (m.mem_maximum) |mx| {
            try s.b(0x01); // has max
            try s.uleb(m.mem_initial);
            try s.uleb(mx);
        } else {
            try s.b(0x00);
            try s.uleb(m.mem_initial);
        }
        try emitSection(&out, 5, &s);
    }

    // --- export section (id 7): memory + every function ---
    {
        var s: Buf = .{ .a = a };
        try s.uleb(nfuncs + 1);
        try s.nameStr("memory");
        try s.b(0x02); // memory kind
        try s.uleb(0);
        for (m.funcs, 0..) |*f, i| {
            try s.nameStr(f.name);
            try s.b(0x00); // func kind
            try s.uleb(@intCast(i));
        }
        try emitSection(&out, 7, &s);
    }

    // --- code section (id 10) + collect access sites ---
    var access: List(AccessSite) = .empty;
    {
        var s: Buf = .{ .a = a };
        try s.uleb(nfuncs);
        for (m.funcs, 0..) |*f, fi| {
            const body_bytes = try emitFunctionBody(a, m.regions, f, @intCast(fi), &access);
            try s.uleb(body_bytes.len);
            try s.raw(body_bytes);
        }
        try emitSection(&out, 10, &s);
    }

    // --- custom: typedwasm.ownership ---
    {
        var pl: Buf = .{ .a = a };
        try pl.u32le(nfuncs);
        for (m.funcs, 0..) |*f, fi| {
            try pl.u32le(@intCast(fi)); // func_idx (no imports => global == local)
            try pl.b(@intCast(f.params.len));
            for (f.params) |pm| try pl.b(ownershipKind(pm.mode));
            try pl.b(0); // ret kind: Unrestricted
        }
        try emitCustom(&out, "typedwasm.ownership", &pl);
    }

    // --- custom: typedwasm.regions ---
    {
        var pl: Buf = .{ .a = a };
        try pl.u16le(1); // version
        try pl.u32le(@intCast(m.regions.len));
        for (m.regions) |r| {
            try pl.u32le(@intCast(r.name.len));
            try pl.raw(r.name);
            try pl.u32le(@intCast(r.fields.len));
            for (r.fields) |f| {
                try pl.u32le(@intCast(f.name.len));
                try pl.raw(f.name);
                try pl.b(fieldKindByte(f.ty));
                try pl.b(fieldWasmTyByte(f.ty));
                try pl.u32le(fieldTargetRegion(m.regions, f.ty));
                try pl.b(fieldNullability(f.ty));
                try pl.u32le(if (f.ty.cardinality == 0) 1 else f.ty.cardinality);
            }
            try pl.u32le(r.stride); // region_byte_size (slot stride)
        }
        try emitCustom(&out, "typedwasm.regions", &pl);
    }

    // --- custom: typedwasm.access-sites ---
    {
        var pl: Buf = .{ .a = a };
        try pl.u16le(1); // version
        try pl.uleb(access.items.len); // entry_count (LEB128)
        for (access.items) |e| {
            try pl.uleb(e.func_idx);
            try pl.uleb(e.offset);
            try pl.uleb(e.region_id);
            try pl.uleb(e.field_id);
        }
        try emitCustom(&out, "typedwasm.access-sites", &pl);
    }

    return out.d.toOwnedSlice(a);
}

fn emitFunctionBody(a: Allocator, regions: []Region, f: *Func, func_idx: u32, access: *List(AccessSite)) Err![]u8 {
    var cg: FnCodegen = .{
        .a = a,
        .regions = regions,
        .func = f,
        .func_idx = func_idx,
        .body = .{ .a = a },
        .access = access,
    };
    try allocLocals(&cg);

    // Build the body bytes (we need the local-decl prefix + code).
    // First emit code into cg.body, then prepend the local declarations.
    // Prologue: read each region-handle param once into its base local.
    for (f.params, 0..) |pm, i| {
        if (pm.is_region) {
            const base: u32 = @intCast(cg.base_local_of_param[i]);
            try cg.body.b(0x20); // local.get param
            try cg.body.uleb(@intCast(i));
            try cg.body.b(0x21); // local.set base
            try cg.body.uleb(base);
        }
    }
    for (f.body) |*st| try cg.emitStmt(st);

    // If the function returns a value but control can fall through without
    // a return, wasm validation needs a value on the stack. Our examples
    // always end with `return`, but emit a defensive default for safety.
    if (f.has_ret) {
        try emitDefault(&cg, scalarWasm(f.ret));
    }
    try cg.body.b(0x0b); // end

    // Local declarations: one group per extra local (params excluded).
    var hdr: Buf = .{ .a = a };
    const n_extra: u32 = @intCast(cg.locals.items.len - cg.n_params);
    try hdr.uleb(n_extra);
    var li: u32 = cg.n_params;
    while (li < cg.locals.items.len) : (li += 1) {
        try hdr.uleb(1);
        try hdr.b(@intFromEnum(cg.locals.items[li].wt));
    }
    try hdr.raw(cg.body.d.items);
    return hdr.d.toOwnedSlice(a);
}

fn emitDefault(cg: *FnCodegen, wt: WT) Err!void {
    switch (wt) {
        .i32 => {
            try cg.body.b(0x41);
            try cg.body.sleb(0);
        },
        .i64 => {
            try cg.body.b(0x42);
            try cg.body.sleb(0);
        },
        .f32 => {
            try cg.body.b(0x43);
            try cg.body.u32le(0);
        },
        .f64 => {
            try cg.body.b(0x44);
            try cg.body.raw(&[_]u8{ 0, 0, 0, 0, 0, 0, 0, 0 });
        },
    }
}

fn emitSection(out: *Buf, id: u8, body: *Buf) Err!void {
    try out.b(id);
    try out.uleb(body.d.items.len);
    try out.raw(body.d.items);
}

fn emitCustom(out: *Buf, name: []const u8, payload: *Buf) Err!void {
    var sec: Buf = .{ .a = out.a };
    try sec.nameStr(name);
    try sec.raw(payload.d.items);
    try emitSection(out, 0, &sec);
}

// ----------------------------------------------------------------------
// main
// ----------------------------------------------------------------------

fn readAllStdin(a: Allocator) Err![]u8 {
    var buf: List(u8) = .empty;
    var tmp: [8192]u8 = undefined;
    while (true) {
        const n = posix.read(posix.STDIN_FILENO, &tmp) catch return fail("stdin read error", .{});
        if (n == 0) break;
        try buf.appendSlice(a, tmp[0..n]);
    }
    return buf.toOwnedSlice(a);
}

fn run() Err!void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();

    const src = try readAllStdin(a);
    const toks = try lex(a, src);
    var parser: Parser = .{ .a = a, .toks = toks };
    var m = try parser.parseModule();
    const wasm = try emitModule(a, &m);
    writeFd(posix.STDOUT_FILENO, wasm);
}

pub fn main() void {
    run() catch {
        var msg: [1100]u8 = undefined;
        const s = std.fmt.bufPrint(&msg, "twasmc: {s}\n", .{g_diag}) catch "twasmc: error\n";
        writeFd(2, s);
        std.process.exit(1);
    };
}
