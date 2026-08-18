// zig-url: a WHATWG-URL parser tuned for speed, mirroring Ada's
// (ada-url/ada) observable behavior for `ada::parse<ada::url_aggregator>`
// with no base URL: same accept/reject decisions, same normalized href.
//
// Zero-allocation design: the caller provides output + scratch buffers.
//   out:     >= 6*input.len + 96*min(input.len, 16384) + 2048 bytes
//              (UTS-46 mapping + punycode worst case is ~96x the host)
//   scratch: >= input.len + 368*min(input.len, 49152) + 512 bytes
//              (IDNA tables need 368 bytes per encoded host byte, worst case)
// Returns the normalized href slice (inside `out`), or null if invalid.

const std = @import("std");
const builtin = @import("builtin");
const idna = @import("idna.zig");

// ---------------------------------------------------------------- tables

const lower: [256]u8 = blk: {
    var t: [256]u8 = undefined;
    for (0..256) |i| t[i] = if (i >= 'A' and i <= 'Z') @intCast(i + 32) else @intCast(i);
    break :blk t;
};

const hex_val: [256]u8 = blk: {
    var t = [_]u8{0xFF} ** 256;
    for ("0123456789", 0..) |c, i| t[c] = @intCast(i);
    for ("abcdef", 0..) |c, i| t[c] = @intCast(10 + i);
    for ("ABCDEF", 0..) |c, i| t[c] = @intCast(10 + i);
    break :blk t;
};

// encode-set bits
const SET_C0: u8 = 1;
const SET_FRAG: u8 = 2;
const SET_QUERY: u8 = 4;
const SET_SQUERY: u8 = 8;
const SET_PATH: u8 = 16;
const SET_USERINFO: u8 = 32;

const enc: [256]u8 = blk: {
    var t = [_]u8{0} ** 256;
    for (0..256) |c| {
        var m: u8 = 0;
        if (c < 0x20 or c >= 0x7F) m = 0x3F; // C0 control set: in every set
        // fragment extra: space " < > `
        if (c == ' ' or c == '"' or c == '<' or c == '>' or c == '`') m |= SET_FRAG;
        // query extra: space " # < >
        const q = c == ' ' or c == '"' or c == '#' or c == '<' or c == '>';
        if (q) m |= SET_QUERY | SET_SQUERY;
        if (c == '\'') m |= SET_SQUERY;
        // path extra: query + ? ^ ` { }
        const p = q or c == '?' or c == '^' or c == '`' or c == '{' or c == '}';
        if (p) m |= SET_PATH;
        // userinfo extra: path + / : ; = @ [ \ ] |
        if (p or c == '/' or c == ':' or c == ';' or c == '=' or c == '@' or
            c == '[' or c == '\\' or c == ']' or c == '|') m |= SET_USERINFO;
        t[c] = @intCast(m);
    }
    break :blk t;
};

// classification bits for hot-path scans
const CL_HOST_PLAIN: u8 = 1; // lowercase domain char, no '%', not forbidden, < 0x80
const CL_PATH_PLAIN: u8 = 2; // no path-encode, not '.', not '%', not '\\'
const CL_QUERY_PLAIN: u8 = 4; // no query-encode (non-special variant)
const CL_SQUERY_PLAIN: u8 = 8; // no special-query-encode
const CL_FRAG_PLAIN: u8 = 16;
const CL_TABNL: u8 = 32; // \t \n \r
const CL_DIGITISH: u8 = 64; // 0-9 a-f x  (lowercase only)
const CL_USERINFO_PLAIN: u8 = 128;

const cls: [256]u8 = blk: {
    var t = [_]u8{0} ** 256;
    for (0..256) |c| {
        var m: u8 = 0;
        const is_forbidden_domain = c <= 0x20 or c == 0x7F or c >= 0x80 or
            c == '#' or c == '/' or c == ':' or c == '<' or c == '>' or c == '?' or
            c == '@' or c == '[' or c == '\\' or c == ']' or c == '^' or c == '|' or c == '%';
        const is_upper = c >= 'A' and c <= 'Z';
        if (!is_forbidden_domain and !is_upper) m |= CL_HOST_PLAIN;
        if (enc[c] & SET_PATH == 0 and c != '.' and c != '%' and c != '\\') m |= CL_PATH_PLAIN;
        if (enc[c] & SET_QUERY == 0) m |= CL_QUERY_PLAIN;
        if (enc[c] & SET_SQUERY == 0) m |= CL_SQUERY_PLAIN;
        if (enc[c] & SET_FRAG == 0) m |= CL_FRAG_PLAIN;
        if (c == 9 or c == 10 or c == 13) m |= CL_TABNL;
        if ((c >= '0' and c <= '9') or (c >= 'a' and c <= 'f') or c == 'x') m |= CL_DIGITISH;
        if (enc[c] & SET_USERINFO == 0 and c != ':') m |= CL_USERINFO_PLAIN;
        t[c] = m;
    }
    break :blk t;
};

fn isForbiddenOpaqueHost(c: u8) bool {
    return c == 0 or c == 9 or c == 10 or c == 13 or c == ' ' or c == '#' or
        c == '/' or c == ':' or c == '<' or c == '>' or c == '?' or c == '@' or
        c == '[' or c == '\\' or c == ']' or c == '^' or c == '|';
}

// ---------------------------------------------------------------- writer

const W = struct {
    buf: []u8,
    n: usize = 0,

    inline fn put(self: *W, c: u8) void {
        self.buf[self.n] = c;
        self.n += 1;
    }
    inline fn putStr(self: *W, s: []const u8) void {
        const n = s.len;
        const d = self.buf.ptr + self.n;
        if (n <= 64) {
            // inline vector copies beat a memcpy call for short spans
            var i: usize = 0;
            while (i + 32 <= n) : (i += 32) {
                d[i..][0..32].* = s[i..][0..32].*;
            }
            if (i < n) {
                if (n >= 32) {
                    d[n - 32 ..][0..32].* = s[n - 32 ..][0..32].*;
                } else if (n >= 16) {
                    d[0..16].* = s[0..16].*;
                    d[n - 16 ..][0..16].* = s[n - 16 ..][0..16].*;
                } else {
                    while (i < n) : (i += 1) d[i] = s[i];
                }
            }
        } else {
            @memcpy(d[0..n], s);
        }
        self.n += n;
    }
    inline fn putByte3(self: *W, a: u8, b: u8, c: u8) void {
        self.put(a);
        self.put(b);
        self.put(c);
    }
    inline fn putEnc(self: *W, c: u8, set: u8) void {
        if (enc[c] & set != 0) {
            const HEX = "0123456789ABCDEF";
            self.putByte3('%', HEX[c >> 4], HEX[c & 15]);
        } else self.put(c);
    }
    fn putEncStr(self: *W, s: []const u8, set: u8) void {
        for (s) |c| self.putEnc(c, set);
    }
    fn putUint(self: *W, v: u32) void {
        var tmp: [10]u8 = undefined;
        var i: usize = tmp.len;
        var x = v;
        while (true) {
            i -= 1;
            tmp[i] = @intCast('0' + x % 10);
            x /= 10;
            if (x == 0) break;
        }
        self.putStr(tmp[i..]);
    }
};

// ------------------------------------------------------- small scan utils

inline fn indexOf2(hay: []const u8, a: u8, b: u8) ?usize {
    const ia = std.mem.indexOfScalar(u8, hay, a) orelse return std.mem.indexOfScalar(u8, hay, b);
    const ib = std.mem.indexOfScalar(u8, hay, b) orelse return ia;
    return @min(ia, ib);
}

inline fn indexOf3(hay: []const u8, a: u8, b: u8, c: u8) ?usize {
    var best: ?usize = std.mem.indexOfScalar(u8, hay, a);
    if (std.mem.indexOfScalar(u8, hay, b)) |i| best = if (best) |cur| @min(cur, i) else i;
    if (std.mem.indexOfScalar(u8, hay, c)) |i| best = if (best) |cur| @min(cur, i) else i;
    return best;
}

// ---------------------------------------------------- SIMD plain scanners
//
// scanPlain finds the first byte that is NOT in the given plain set (i.e.
// the first byte the scalar indexOfNonClass would return), using vector
// compares instead of a per-byte table load. The predicates below are
// derived from `cls`/`enc` above and must match them exactly:
//   host:  c<=0x20 | c>=0x7F | 'A'..'Z' | # / : < > ? @ [ \ ] ^ | %
//   path:  c<=0x20 | c>=0x7F | " # % . < > ? \ ^ ` { }
//   query: c<=0x20 | c>=0x7F | " # < >
//  squery: query + '
//   frag:  c<=0x20 | c>=0x7F | " < > `
// pathenc: the SET_PATH percent-encode set (c<0x20 | c>=0x7F | sp " # < > ? ^ ` { })
const PlainSet = enum { host, path, query, squery, frag, pathenc };

// is byte c plain for the given set (mirrors the cls/enc tables exactly)
fn plainBoolTable(comptime set: PlainSet) [256]bool {
    var t: [256]bool = undefined;
    for (0..256) |c| {
        t[c] = switch (set) {
            .host => cls[c] & CL_HOST_PLAIN != 0,
            .path => cls[c] & CL_PATH_PLAIN != 0,
            .query => cls[c] & CL_QUERY_PLAIN != 0,
            .squery => cls[c] & CL_SQUERY_PLAIN != 0,
            .frag => cls[c] & CL_FRAG_PLAIN != 0,
            .pathenc => enc[c] & SET_PATH == 0,
        };
    }
    return t;
}

// NEON tbl classifier tables (simdjson nibble trick):
//   plain(c) == (lo_tab[c & 15] & hi_tab[c >> 4]) != 0
// Built by grouping hi-nibble rows that share the same 16-bit plain-lo
// mask; each distinct nonzero mask gets one bit (max 8 groups).
const TblPair = struct { lo: [16]u8, hi: [16]u8 };

fn tblTables(comptime plain: [256]bool) TblPair {
    @setEvalBranchQuota(10000);
    var lo_tab = [_]u8{0} ** 16;
    var hi_tab = [_]u8{0} ** 16;
    var group_masks: [8]u16 = undefined;
    var ng: usize = 0;
    for (0..16) |hi| {
        var m: u16 = 0;
        for (0..16) |l| {
            if (plain[hi * 16 + l]) m |= @as(u16, 1) << @intCast(l);
        }
        if (m == 0) continue;
        var g: usize = 0;
        while (g < ng and group_masks[g] != m) g += 1;
        if (g == ng) {
            if (ng >= 8) @compileError("tbl classifier: more than 8 row groups");
            group_masks[ng] = m;
            ng += 1;
            var l: usize = 0;
            while (l < 16) : (l += 1) {
                if ((m >> @intCast(l)) & 1 != 0) lo_tab[l] |= @as(u8, 1) << @intCast(g);
            }
        }
        hi_tab[hi] |= @as(u8, 1) << @intCast(g);
    }
    return .{ .lo = lo_tab, .hi = hi_tab };
}

const use_tbl = builtin.cpu.arch == .aarch64;

inline fn tblLookup(tab: @Vector(16, u8), idx: @Vector(16, u8)) @Vector(16, u8) {
    return asm ("tbl %[r].16b, {%[t].16b}, %[i].16b"
        : [r] "=w" (-> @Vector(16, u8)),
        : [t] "w" (tab),
        [i] "w" (idx),
    );
}

const V16u8 = @Vector(16, u8);

// NEON movemask of the non-plain lanes of c: lane j contributes one bit at
// 4*j+3 (so @ctz(m) >> 2 is the first non-plain index; m == 0 == all plain).
// cmeq+shrn+fmov = 3 instructions, vs the ~5 LLVM emits for a
// <16 x i1> -> i16 bitcast. aarch64-only: callers are use_tbl-guarded.
inline fn nonPlainMask16(comptime lo_tab: V16u8, comptime hi_tab: V16u8, c: V16u8) u64 {
    var plain = plainLanes(lo_tab, hi_tab, c);
    return asm ("cmeq %[x].16b, %[x].16b, #0\n\tshrn %[x].8b, %[x].8h, #4\n\tumov %[r], %[x].d[0]"
        : [x] "+w" (plain),
        [r] "=r" (-> u64),
    );
}

// per-16-byte-lane plain mask for a chunk pair helper
inline fn plainLanes(comptime lo_tab: V16u8, comptime hi_tab: V16u8, c: V16u8) V16u8 {
    const nib: V16u8 = @splat(0x0F);
    const sh: @Vector(16, u3) = @splat(4);
    return tblLookup(lo_tab, c & nib) & tblLookup(hi_tab, c >> sh);
}

// aarch64 tbl scan: first non-plain index, or hay.len. Requires hay.len >= 16.
fn scanPlainTbl(comptime set: PlainSet, hay: []const u8) usize {
    const T = comptime tblTables(plainBoolTable(set));
    const lo_tab: V16u8 = T.lo;
    const hi_tab: V16u8 = T.hi;
    const n = hay.len;
    var i: usize = 0;
    while (i + 64 <= n) : (i += 64) {
        const c0: V16u8 = hay[i..][0..16].*;
        const c1: V16u8 = hay[i + 16 ..][0..16].*;
        const c2: V16u8 = hay[i + 32 ..][0..16].*;
        const c3: V16u8 = hay[i + 48 ..][0..16].*;
        const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
        const m1 = nonPlainMask16(lo_tab, hi_tab, c1);
        const m2 = nonPlainMask16(lo_tab, hi_tab, c2);
        const m3 = nonPlainMask16(lo_tab, hi_tab, c3);
        if (((m0 | m1) | (m2 | m3)) != 0) {
            if (m0 != 0) return i + (@ctz(m0) >> 2);
            if (m1 != 0) return i + 16 + (@ctz(m1) >> 2);
            if (m2 != 0) return i + 32 + (@ctz(m2) >> 2);
            return i + 48 + (@ctz(m3) >> 2);
        }
    }
    while (i + 32 <= n) : (i += 32) {
        const c0: V16u8 = hay[i..][0..16].*;
        const c1: V16u8 = hay[i + 16 ..][0..16].*;
        const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
        const m1 = nonPlainMask16(lo_tab, hi_tab, c1);
        if ((m0 | m1) != 0) {
            if (m0 != 0) return i + (@ctz(m0) >> 2);
            return i + 16 + (@ctz(m1) >> 2);
        }
    }
    while (i + 16 <= n) : (i += 16) {
        const c0: V16u8 = hay[i..][0..16].*;
        const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
        if (m0 != 0) return i + (@ctz(m0) >> 2);
    }
    if (i < n) {
        // final overlapping block ([0, i) already verified plain)
        const c0: V16u8 = hay[n - 16 ..][0..16].*;
        const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
        if (m0 != 0) {
            const idx = n - 16 + (@ctz(m0) >> 2);
            return if (idx < i) i else idx;
        }
    }
    return n;
}

fn scanPlainScalar(comptime set: PlainSet, hay: []const u8) usize {
    const plain = comptime plainBoolTable(set);
    for (hay, 0..) |c, i| {
        if (!plain[c]) return i;
    }
    return hay.len;
}

inline fn nonPlain(comptime set: PlainSet, comptime N: usize, c: @Vector(N, u8)) @Vector(N, bool) {
    const V = @Vector(N, u8);
    const s1: V = @splat(1);
    var m = (c <= @as(V, @splat(0x20))) | (c >= @as(V, @splat(0x7F)));
    switch (set) {
        .host => {
            const upper = (c -% @as(V, @splat('A'))) <= @as(V, @splat(25));
            const brack = (c -% @as(V, @splat(0x5B))) <= @as(V, @splat(3)); // [ \ ] ^
            const gtq = (c | s1) == @as(V, @splat(0x3F)); // > ?
            m |= (upper | brack) | (gtq |
                (c == @as(V, @splat('#'))) | (c == @as(V, @splat('/'))) |
                (c == @as(V, @splat(':'))) | (c == @as(V, @splat('<'))) |
                (c == @as(V, @splat('@'))) | (c == @as(V, @splat('|'))) |
                (c == @as(V, @splat('%'))));
        },
        .path => {
            const dq = (c | s1) == @as(V, @splat(0x23)); // " #
            const gtq = (c | s1) == @as(V, @splat(0x3F)); // > ?
            const bs = (c | @as(V, @splat(2))) == @as(V, @splat(0x5E)); // \ ^
            m |= (dq | gtq) | (bs |
                (c == @as(V, @splat('%'))) | (c == @as(V, @splat('.'))) |
                (c == @as(V, @splat('<'))) | (c == @as(V, @splat('`'))) |
                (c == @as(V, @splat('{'))) | (c == @as(V, @splat('}'))));
        },
        .query => {
            const dq = (c | s1) == @as(V, @splat(0x23)); // " #
            m |= dq | (c == @as(V, @splat('<'))) | (c == @as(V, @splat('>')));
        },
        .squery => {
            const dq = (c | s1) == @as(V, @splat(0x23)); // " #
            m |= (dq | (c == @as(V, @splat(0x27)))) |
                ((c == @as(V, @splat('<'))) | (c == @as(V, @splat('>'))));
        },
        .frag => {
            m |= ((c == @as(V, @splat('"'))) | (c == @as(V, @splat('`')))) |
                ((c == @as(V, @splat('<'))) | (c == @as(V, @splat('>'))));
        },
        .pathenc => {
            const dq = (c | s1) == @as(V, @splat(0x23)); // " #
            const gtq = (c | s1) == @as(V, @splat(0x3F)); // > ?
            m |= (dq | gtq) |
                ((c == @as(V, @splat('<'))) | (c == @as(V, @splat('^')))) |
                ((c == @as(V, @splat('`'))) | (c == @as(V, @splat('{')))) |
                (c == @as(V, @splat('}')));
        },
    }
    return m;
}

// index of the first non-plain byte, or hay.len if all plain
fn scanPlain(comptime set: PlainSet, hay: []const u8) usize {
    const n = hay.len;
    if (comptime use_tbl) {
        if (n >= 16) return scanPlainTbl(set, hay);
        return scanPlainScalar(set, hay);
    }
    var i: usize = 0;
    if (n >= VLEN) {
        while (i + VLEN <= n) : (i += VLEN) {
            const chunk: Vu8 = hay[i..][0..VLEN].*;
            const bits: u32 = @bitCast(nonPlain(set, VLEN, chunk));
            if (bits != 0) return i + @ctz(bits);
        }
        if (i < n) {
            // final overlapping block ([0, i) already verified plain)
            const chunk: Vu8 = hay[n - VLEN ..][0..VLEN].*;
            const bits: u32 = @bitCast(nonPlain(set, VLEN, chunk));
            if (bits != 0) {
                const idx = n - VLEN + @ctz(bits);
                return if (idx < i) i else idx;
            }
        }
        return n;
    }
    if (n >= 16) {
        const V16 = @Vector(16, u8);
        var chunk: V16 = hay[0..16].*;
        var bits: u16 = @bitCast(nonPlain(set, 16, chunk));
        if (bits != 0) return @ctz(bits);
        chunk = hay[n - 16 ..][0..16].*;
        bits = @bitCast(nonPlain(set, 16, chunk));
        if (bits != 0) return n - 16 + @ctz(bits); // [0,16) already plain
        return n;
    }
    return scanPlainScalar(set, hay);
}

// ------------------------------------------------------- SIMD-ish scanners

const VLEN = 32;
const Vu8 = @Vector(VLEN, u8);

const Prescan = struct { hash: ?usize, tabnl: bool };

// one fused pass over the input: position of first '#', and whether any
// \t \n \r is present. The vector pass is deliberately coarse — tabnl
// candidates are detected as the range 9..13 (which also matches 11/12) —
// and only pays for a precise scalar analysis when something fired.
fn prescan(in: []const u8) Prescan {
    const n = in.len;
    if (n >= VLEN) {
        const vh: Vu8 = @splat('#');
        const v9: Vu8 = @splat(9);
        const v13: Vu8 = @splat(13);
        var acc: u32 = 0;
        var i: usize = 0;
        while (i + VLEN <= n) : (i += VLEN) {
            const chunk: Vu8 = in[i..][0..VLEN].*;
            const hit = (chunk == vh) | ((chunk >= v9) & (chunk <= v13));
            acc |= @as(u32, @bitCast(hit));
        }
        if (i < n) {
            const chunk: Vu8 = in[n - VLEN ..][0..VLEN].*;
            const hit = (chunk == vh) | ((chunk >= v9) & (chunk <= v13));
            acc |= @as(u32, @bitCast(hit));
        }
        if (acc == 0) return .{ .hash = null, .tabnl = false };
    }
    return prescanSlow(in);
}

fn prescanSlow(in: []const u8) Prescan {
    var hash: ?usize = null;
    var tabnl = false;
    for (in, 0..) |c, i| {
        if (c == 9 or c == 10 or c == 13) tabnl = true;
        if (c == '#' and hash == null) hash = i;
    }
    return .{ .hash = hash, .tabnl = tabnl };
}

// first index of any of {a, b, c(|null)} — vectorized; hay.len if none.
fn indexOfAnyV(hay: []const u8, a: u8, b: u8, c: ?u8) usize {
    const n = hay.len;
    if (n >= VLEN) {
        const va: Vu8 = @splat(a);
        const vb: Vu8 = @splat(b);
        const vc: Vu8 = @splat(c orelse 0);
        var i: usize = 0;
        while (i + VLEN <= n) : (i += VLEN) {
            const chunk: Vu8 = hay[i..][0..VLEN].*;
            var m = (chunk == va) | (chunk == vb);
            if (c != null) m = m | (chunk == vc);
            const bits: std.meta.Int(.unsigned, VLEN) = @bitCast(m);
            if (bits != 0) return i + @ctz(bits);
        }
        if (i < n) {
            // final overlapping block (re-scans up to VLEN-1 bytes; safe)
            const chunk: Vu8 = hay[n - VLEN ..][0..VLEN].*;
            var m = (chunk == va) | (chunk == vb);
            if (c != null) m = m | (chunk == vc);
            const bits: std.meta.Int(.unsigned, VLEN) = @bitCast(m);
            if (bits != 0) {
                const idx = n - VLEN + @ctz(bits);
                return if (idx < i) i else idx; // main loop already cleared [0, i)
            }
        }
        return n;
    }
    if (n >= 16) {
        // one or two overlapping 16-byte vector blocks
        const V16 = @Vector(16, u8);
        const va: V16 = @splat(a);
        const vb: V16 = @splat(b);
        const vc: V16 = @splat(c orelse 0);
        var chunk: V16 = hay[0..16].*;
        var m = (chunk == va) | (chunk == vb);
        if (c != null) m = m | (chunk == vc);
        var bits: u16 = @bitCast(m);
        if (bits != 0) return @ctz(bits);
        chunk = hay[n - 16 ..][0..16].*;
        m = (chunk == va) | (chunk == vb);
        if (c != null) m = m | (chunk == vc);
        bits = @bitCast(m);
        if (bits != 0) return n - 16 + @ctz(bits); // block 1 already cleared [0, 16)
        return n;
    }
    for (hay, 0..) |ch, i| {
        if (ch == a or ch == b or (c != null and ch == c.?)) return i;
    }
    return n;
}

inline fn eqlIC(a: []const u8, comptime b: []const u8) bool {
    if (a.len != b.len) return false;
    inline for (b, 0..) |bc, i| {
        if (lower[a[i]] != bc) return false;
    }
    return true;
}

// ------------------------------------------------------------- scheme

const SchemeKind = enum { http, https, ws, wss, ftp, file, other };

const SchemeInfo = struct { kind: SchemeKind, special: bool, default_port: ?u16 };

fn schemeInfo(s: []const u8) SchemeInfo {
    if (eqlIC(s, "http")) return .{ .kind = .http, .special = true, .default_port = 80 };
    if (eqlIC(s, "https")) return .{ .kind = .https, .special = true, .default_port = 443 };
    if (eqlIC(s, "ws")) return .{ .kind = .ws, .special = true, .default_port = 80 };
    if (eqlIC(s, "wss")) return .{ .kind = .wss, .special = true, .default_port = 443 };
    if (eqlIC(s, "ftp")) return .{ .kind = .ftp, .special = true, .default_port = 21 };
    if (eqlIC(s, "file")) return .{ .kind = .file, .special = true, .default_port = null };
    return .{ .kind = .other, .special = false, .default_port = null };
}

// ------------------------------------------------------------- IPv4

// mirrors ada detail::parse_ipv4_number
fn parseIpv4Number(s: []const u8, p: *usize, value: *u64) bool {
    const start = p.*;
    const end = s.len;
    if (start >= end) return false;
    if (end - start >= 2 and s[start] == '0' and (s[start + 1] | 0x20) == 'x') {
        var q = start + 2;
        if (q == end or s[q] == '.') {
            value.* = 0;
            p.* = q;
            return true;
        }
        var v: u64 = 0;
        var digits: usize = 0;
        while (q < end and s[q] != '.') {
            const nib = hex_val[s[q]];
            if (nib == 0xFF) return false;
            if (v > (0xFFFFFFFF >> 4)) return false;
            v = (v << 4) | nib;
            q += 1;
            digits += 1;
        }
        if (digits == 0) return false;
        value.* = v;
        p.* = q;
        return true;
    }
    if (end - start >= 2 and s[start] == '0' and s[start + 1] >= '0' and s[start + 1] <= '9') {
        var q = start + 1;
        var v: u64 = 0;
        while (q < end and s[q] != '.') {
            const c = s[q];
            if (c < '0' or c > '7') return false;
            if (v > (0xFFFFFFFF >> 3)) return false;
            v = (v << 3) | @as(u64, c - '0');
            q += 1;
        }
        value.* = v;
        p.* = q;
        return true;
    }
    if (s[start] < '0' or s[start] > '9') return false;
    var q = start;
    var v: u64 = s[q] - '0';
    q += 1;
    while (q < end and s[q] != '.') {
        const c = s[q];
        if (c < '0' or c > '9') return false;
        if (v > 429496729) return false;
        v = v * 10 + @as(u64, c - '0');
        if (v > 0xFFFFFFFF) return false;
        q += 1;
    }
    value.* = v;
    p.* = q;
    return true;
}

fn writeIpv4(w: *W, v: u64) void {
    w.putUint(@intCast((v >> 24) & 0xFF));
    w.put('.');
    w.putUint(@intCast((v >> 16) & 0xFF));
    w.put('.');
    w.putUint(@intCast((v >> 8) & 0xFF));
    w.put('.');
    w.putUint(@intCast(v & 0xFF));
}

// mirrors ada url_aggregator::parse_ipv4 (input: lowercased decoded host)
fn parseIpv4Into(w: *W, s0: []const u8) bool {
    var s = s0;
    if (s.len == 0) return false;
    if (s[s.len - 1] == '.') {
        s = s[0 .. s.len - 1];
        if (s.len == 0) return false;
    }
    var p: usize = 0;
    const end = s.len;
    var ipv4: u64 = 0;
    var digit_count: usize = 0;
    var finished = false;
    while (digit_count < 4 and p < end) : (digit_count += 1) {
        var segment: u64 = 0;
        if (!parseIpv4Number(s, &p, &segment)) return false;
        if (p >= end) {
            const shift: u6 = @intCast(32 - digit_count * 8);
            if (segment >= (@as(u64, 1) << shift)) return false;
            ipv4 = (ipv4 << shift) | segment;
            finished = true;
            break;
        }
        if (segment > 255 or s[p] != '.') return false;
        ipv4 = (ipv4 << 8) | segment;
        p += 1;
    }
    if (!finished and (digit_count != 4 or p != end)) return false;
    writeIpv4(w, ipv4);
    return true;
}

// mirrors ada checkers::is_ipv4 ("ends in a number"; input already lowercase)
fn isIpv4(s0: []const u8) bool {
    var s = s0;
    if (s.len > 0 and s[s.len - 1] == '.') {
        s = s[0 .. s.len - 1];
        if (s.len == 0) return false;
    }
    if (s.len == 0) return false;
    if (cls[s[s.len - 1]] & CL_DIGITISH == 0) return false;
    const label = if (std.mem.lastIndexOfScalar(u8, s, '.')) |d| s[d + 1 ..] else s;
    if (label.len == 0) return false;
    var all_digits = true;
    for (label) |c| {
        if (c < '0' or c > '9') {
            all_digits = false;
            break;
        }
    }
    if (all_digits) return true;
    if (label.len < 2) return false;
    if (label[0] != '0' or label[1] != 'x') return false;
    if (label.len == 2) return true;
    for (label[2..]) |c| {
        const ok = (c >= '0' and c <= '9') or (c >= 'a' and c <= 'f');
        if (!ok) return false;
    }
    return true;
}

// ------------------------------------------------------------- IPv6

fn parseHexPiece(s: []const u8, p: *usize, value: *u16) usize {
    const end = s.len;
    if (p.* == end) return 0;
    const n0 = hex_val[s[p.*]];
    if (n0 == 0xFF) return 0;
    var v: u32 = n0;
    p.* += 1;
    var length: usize = 1;
    if (p.* != end) {
        const n1 = hex_val[s[p.*]];
        if (n1 != 0xFF) {
            v = (v << 4) | n1;
            p.* += 1;
            length += 1;
            if (p.* != end) {
                const n2 = hex_val[s[p.*]];
                if (n2 != 0xFF) {
                    v = (v << 4) | n2;
                    p.* += 1;
                    length += 1;
                    if (p.* != end) {
                        const n3 = hex_val[s[p.*]];
                        if (n3 != 0xFF) {
                            v = (v << 4) | n3;
                            p.* += 1;
                            length += 1;
                        }
                    }
                }
            }
        }
    }
    value.* = @intCast(v);
    return length;
}

// mirrors ada url_aggregator::parse_ipv6
fn parseIpv6(inner: []const u8, address: *[8]u16) bool {
    if (inner.len == 0 or inner.len > 45) return false;
    @memset(address, 0);
    var p: usize = 0;
    const end = inner.len;
    var piece_index: usize = 0;
    var compress: i32 = -1;

    if (inner[0] == ':') {
        if (inner.len == 1 or inner[1] != ':') return false;
        p = 2;
        piece_index = 1;
        compress = 1;
    }
    while (p < end) {
        if (piece_index == 8) return false;
        if (inner[p] == ':') {
            if (compress != -1) return false;
            p += 1;
            piece_index += 1;
            compress = @intCast(piece_index);
            continue;
        }
        var value: u16 = 0;
        const length = parseHexPiece(inner, &p, &value);
        if (p < end and inner[p] == '.') {
            if (length == 0) return false;
            p -= length;
            if (piece_index > 6) return false;
            var numbers_seen: usize = 0;
            while (p < end) {
                if (numbers_seen > 0) {
                    if (inner[p] == '.' and numbers_seen < 4) {
                        p += 1;
                    } else return false;
                }
                if (p == end or inner[p] < '0' or inner[p] > '9') return false;
                var ipv4_piece: u32 = inner[p] - '0';
                p += 1;
                if (p < end and inner[p] >= '0' and inner[p] <= '9') {
                    if (ipv4_piece == 0) return false;
                    ipv4_piece = ipv4_piece * 10 + (inner[p] - '0');
                    p += 1;
                    if (p < end and inner[p] >= '0' and inner[p] <= '9') {
                        ipv4_piece = ipv4_piece * 10 + (inner[p] - '0');
                        p += 1;
                        if (ipv4_piece > 255) return false;
                    }
                }
                address[piece_index] = address[piece_index] * 0x100 + @as(u16, @intCast(ipv4_piece));
                numbers_seen += 1;
                if (numbers_seen == 2 or numbers_seen == 4) piece_index += 1;
            }
            if (numbers_seen != 4) return false;
            break;
        }
        if (length == 0) return false;
        if (p < end and inner[p] == ':') {
            p += 1;
            if (p == end) return false;
        } else if (p < end) return false;
        address[piece_index] = value;
        piece_index += 1;
    }
    if (compress != -1) {
        const c: usize = @intCast(compress);
        const right = piece_index - c;
        if (right > 0) {
            const dest = 8 - right;
            const src = c;
            if (dest != src) {
                var i = right;
                while (i > 0) : (i -= 1) {
                    address[dest + i - 1] = address[src + i - 1];
                    address[src + i - 1] = 0;
                }
            }
        }
    } else if (piece_index != 8) return false;
    return true;
}

fn writeHexLower(w: *W, v: u16) void {
    const HEXL = "0123456789abcdef";
    if (v >= 0x1000) w.put(HEXL[(v >> 12) & 0xF]);
    if (v >= 0x100) w.put(HEXL[(v >> 8) & 0xF]);
    if (v >= 0x10) w.put(HEXL[(v >> 4) & 0xF]);
    w.put(HEXL[v & 0xF]);
}

// mirrors ada serializers::ipv6 (includes brackets)
fn writeIpv6(w: *W, addr: *const [8]u16) void {
    var best_start: usize = 8;
    var best_len: usize = 0;
    var i: usize = 0;
    while (i < 8) {
        if (addr[i] == 0) {
            var j = i;
            while (j < 8 and addr[j] == 0) j += 1;
            if (j - i > best_len) {
                best_len = j - i;
                best_start = i;
            }
            i = j;
        } else i += 1;
    }
    if (best_len == 8) {
        w.putStr("[::]");
        return;
    }
    const compress = best_len >= 2;
    w.put('[');
    var need_sep = false;
    i = 0;
    while (i < 8) {
        if (compress and i == best_start) {
            w.putStr("::");
            i += best_len;
            need_sep = false;
            continue;
        }
        if (need_sep) w.put(':');
        writeHexLower(w, addr[i]);
        need_sep = true;
        i += 1;
    }
    w.put(']');
}

// ------------------------------------------------------------- host

// special-scheme host parsing; writes normalized host into w.
// Full UTS-46/IDNA via idna.domainToAscii (byte-exact Ada parity):
// percent-decode, mapping, NFC normalization, punycode, forbidden check.
fn parseHostSpecial(w: *W, host_raw: []const u8, scratch: []u8) bool {
    if (host_raw.len == 0) return false;
    if (host_raw[0] == '[') {
        if (host_raw[host_raw.len - 1] != ']') return false;
        var addr: [8]u16 = undefined;
        if (!parseIpv6(host_raw[1 .. host_raw.len - 1], &addr)) return false;
        writeIpv6(w, &addr);
        return true;
    }
    // Percent-decoding shrinks input at most 3x, so an encoded host longer
    // than 3*16384 bytes always decodes beyond max_domain_input_bytes and is
    // rejected by UTS-46 toASCII anyway.
    if (host_raw.len > 3 * idna.max_domain_input_bytes) return false;
    const h = host_raw.len;
    const idna_out = scratch[0 .. 96 * h + 64];
    const idna_scratch = scratch[96 * h + 64 ..][0 .. 272 * h + 192];
    const res = idna.domainToAscii(host_raw, idna_out, idna_scratch) orelse return false;
    if (isIpv4(res)) return parseIpv4Into(w, res);
    w.putStr(res);
    return true;
}

// non-special-scheme opaque host
fn parseHostOpaque(w: *W, host: []const u8) bool {
    for (host) |c| {
        if (isForbiddenOpaqueHost(c)) return false;
    }
    w.putEncStr(host, SET_C0);
    return true;
}

// ------------------------------------------------------------- path pieces

inline fn eqPct2e(s: []const u8) bool {
    return s.len == 3 and s[0] == '%' and s[1] == '2' and (s[2] | 0x20) == 'e';
}

inline fn isSingleDot(seg: []const u8) bool {
    if (seg.len == 1) return seg[0] == '.';
    if (seg.len == 3) return eqPct2e(seg);
    return false;
}

inline fn isDoubleDot(seg: []const u8) bool {
    if (seg.len == 2) return seg[0] == '.' and seg[1] == '.';
    if (seg.len == 4) {
        return (seg[0] == '.' and eqPct2e(seg[1..4])) or
            (eqPct2e(seg[0..3]) and seg[3] == '.');
    }
    if (seg.len == 6) return eqPct2e(seg[0..3]) and eqPct2e(seg[3..6]);
    return false;
}

inline fn isWindowsDriveLetter(seg: []const u8) bool {
    return seg.len == 2 and ((seg[0] | 0x20) >= 'a' and (seg[0] | 0x20) <= 'z') and
        (seg[1] == ':' or seg[1] == '|');
}

// shorten path in w starting at path_start (mimics helpers::shorten_path):
// erase from last '/' to end; for file: a lone normalized drive segment stays.
fn shortenPath(w: *W, path_start: usize, is_file: bool) void {
    const region = w.buf[path_start..w.n];
    if (is_file and region.len == 3 and region[0] == '/' and
        ((region[1] | 0x20) >= 'a' and (region[1] | 0x20) <= 'z') and region[2] == ':')
    {
        return;
    }
    if (std.mem.lastIndexOfScalar(u8, region, '/')) |idx| {
        w.n = path_start + idx;
    }
}

// process pathview (already excludes query/fragment); separators are '/'
// plus '\\' for special schemes. Writes into w starting at path_start.
fn parsePath(w: *W, pathview: []const u8, special: bool, is_file: bool) void {
    parsePathAt(w, pathview, special, is_file, w.n);
}

// parsePath with an explicit path start: used by relative resolution where
// leading base-path segments were already written into w, so that '..'
// can shorten across them.
fn parsePathAt(w: *W, pathview: []const u8, special: bool, is_file: bool, path_start: usize) void {
    var pos: usize = 0;
    if (pathview.len > 0 and (pathview[0] == '/' or (special and pathview[0] == '\\'))) pos = 1;
    while (true) {
        const seg_start = pos;
        if (special) {
            pos += indexOfAnyV(pathview[pos..], '/', '\\', null);
        } else {
            pos += std.mem.indexOfScalar(u8, pathview[pos..], '/') orelse pathview.len - pos;
        }
        const seg = pathview[seg_start..pos];
        const is_last = pos >= pathview.len;
        if (isDoubleDot(seg)) {
            shortenPath(w, path_start, is_file);
            if (is_last) w.put('/');
        } else if (isSingleDot(seg)) {
            if (is_last) w.put('/');
        } else {
            w.put('/');
            if (is_file and w.n == path_start + 1 and isWindowsDriveLetter(seg)) {
                w.put(seg[0]);
                w.put(':');
            } else {
                if (scanPlain(.pathenc, seg) != seg.len)
                    w.putEncStr(seg, SET_PATH)
                else
                    w.putStr(seg);
            }
        }
        if (is_last) break;
        pos += 1;
    }
}

// ------------------------------------------------------------- public API

pub const HostType = enum { domain, ipv4, ipv6, opaque_host, empty };

/// Component positions inside `href`.
pub const Offsets = struct {
    scheme_end: u32 = 0, // index just past "scheme:"
    auth_start: u32 = 0, // index just past "//" (== scheme_end when no authority)
    cred_start: u32 = 0, // start of userinfo text (before user)
    colon: u32 = 0, // index of the user:pass separator colon; 0 => no password
    cred_end: u32 = 0, // end of userinfo text (before '@')
    has_cred: bool = false,
    host_start: u32 = 0,
    host_end: u32 = 0,
    port_start: u32 = 0, // start of port digits; 0 => no port
    port_end: u32 = 0,
    path_start: u32 = 0,
    path_end: u32 = 0,
    qmark: u32 = 0, // index of '?'; 0 => absent
    hashmark: u32 = 0, // index of '#'; 0 => absent
    opaque_path: bool = false,
    has_authority: bool = false,
    special: bool = false,
    is_file: bool = false,
    host_type: HostType = .empty,
};

pub const Url = struct {
    href: []const u8,
    off: Offsets,

    pub fn protocol(self: *const Url) []const u8 {
        return self.href[0..self.off.scheme_end];
    }
    pub fn scheme(self: *const Url) []const u8 {
        return self.href[0 .. self.off.scheme_end - 1];
    }
    pub fn username(self: *const Url) []const u8 {
        const o = self.off;
        if (!o.has_cred) return "";
        const end = if (o.colon != 0) o.colon else o.cred_end;
        return self.href[o.cred_start..end];
    }
    pub fn password(self: *const Url) []const u8 {
        const o = self.off;
        if (!o.has_cred or o.colon == 0) return "";
        return self.href[o.colon + 1 .. o.cred_end];
    }
    /// host:port
    pub fn host(self: *const Url) []const u8 {
        const o = self.off;
        const end = if (o.port_start != 0) o.port_end else o.host_end;
        return self.href[o.host_start..end];
    }
    pub fn hostname(self: *const Url) []const u8 {
        return self.href[self.off.host_start..self.off.host_end];
    }
    pub fn port(self: *const Url) []const u8 {
        const o = self.off;
        if (o.port_start == 0) return "";
        return self.href[o.port_start..o.port_end];
    }
    pub fn pathname(self: *const Url) []const u8 {
        return self.href[self.off.path_start..self.off.path_end];
    }
    pub fn search(self: *const Url) []const u8 {
        const o = self.off;
        if (o.qmark == 0) return "";
        const end = if (o.hashmark != 0) o.hashmark else @as(u32, @intCast(self.href.len));
        return self.href[o.qmark..end];
    }
    pub fn hash(self: *const Url) []const u8 {
        const o = self.off;
        if (o.hashmark == 0) return "";
        return self.href[o.hashmark..];
    }
    /// scheme://host[:port] for special non-file schemes; for blob: URLs the
    /// origin of the inner http(s) URL (found by re-parsing the pathname,
    /// which normalizes case and elides default ports); "null" otherwise.
    /// For blob URLs, `buf` and `scratch` must satisfy the usual parse
    /// contracts for an input of pathname() length.
    pub fn origin(self: *const Url, buf: []u8, scratch: []u8) []const u8 {
        const o = self.off;
        if (o.special and !o.is_file and o.has_authority) {
            const hp = self.host();
            const se = o.scheme_end;
            @memcpy(buf[0..se], self.href[0..se]);
            buf[se] = '/';
            buf[se + 1] = '/';
            @memcpy(buf[se + 2 .. se + 2 + hp.len], hp);
            return buf[0 .. se + 2 + hp.len];
        }
        if (o.scheme_end == 5 and std.mem.eql(u8, self.href[0..5], "blob:")) {
            const path = self.pathname();
            if (path.len > 0) {
                var inner: Url = undefined;
                if (parseWithBase(path, null, buf, scratch, &inner)) {
                    const ischeme = inner.scheme();
                    if ((std.mem.eql(u8, ischeme, "http") or std.mem.eql(u8, ischeme, "https")) and
                        inner.off.has_authority)
                    {
                        const hp = inner.host();
                        const se = inner.off.scheme_end;
                        // inner href lives in buf; shift the host left to
                        // build "scheme://host" as a prefix (dest < src).
                        buf[se] = '/';
                        buf[se + 1] = '/';
                        std.mem.copyForwards(u8, buf[se + 2 .. se + 2 + hp.len], hp);
                        return buf[0 .. se + 2 + hp.len];
                    }
                }
            }
        }
        return "null";
    }
};

pub fn parse(input0: []const u8, out: []u8, scratch: []u8, res: *Url) bool {
    return parseWithBase(input0, null, out, scratch, res);
}

// Parse `input0` against a base URL (WHATWG URL "basic url parser" with a
// non-null base). `base` must have been produced by a successful parse.
pub fn parseBase(input0: []const u8, base: *const Url, out: []u8, scratch: []u8, res: *Url) bool {
    return parseWithBase(input0, base, out, scratch, res);
}

// serializer rule: host-less URL whose path begins with an empty first
// segment gets "/." prepended (so it cannot be reparsed as an authority).
fn applySlashDotRule(w: *W, pstart: usize, has_authority: bool) void {
    if (has_authority) return;
    if (w.n >= pstart + 2 and w.buf[pstart] == '/' and w.buf[pstart + 1] == '/') {
        const plen = w.n - pstart;
        std.mem.copyBackwards(u8, w.buf[pstart + 2 .. pstart + plen + 2], w.buf[pstart .. pstart + plen]);
        w.buf[pstart] = '/';
        w.buf[pstart + 1] = '.';
        w.n += 2;
    }
}

// Tight single-pass fast path for the dominant absolute-URL shape:
// "http(s)://" + plain lowercase host + plain path [+ plain query]
// [+ plain fragment]. Returns null when the input deviates in any way
// (caller falls back to the general parser, which re-does the work);
// true once the URL is fully parsed. Every accept condition mirrors the
// general path's own bulk branch, so outputs are identical by construction.
fn parseFastAbsolute(in: []const u8, out: []u8, res: *Url) ?bool {
    if (in.len < 8) return null;
    const w8 = std.mem.readInt(u64, in[0..8], .little);
    const sc_https = comptime std.mem.readInt(u64, "https://", .little);
    const sc_http = comptime std.mem.readInt(u64, "http://\x00", .little);
    const sc_http_mask: u64 = 0x00FFFFFFFFFFFFFF;
    var scheme_len: usize = 8;
    if (w8 == sc_https) {
        @branchHint(.likely);
    } else if ((w8 & sc_http_mask) == sc_http) {
        scheme_len = 7;
    } else return null;
    const rest = in[scheme_len..];
    // host: plain lowercase domain chars up to '/' (or end); anything else
    // (port, userinfo, '%', uppercase, non-ASCII, '\', '?', '#') opts out.
    const k = scanHostFast(rest);
    if (k == 0) return null;
    if (k < rest.len and rest[k] != '/') return null;
    const last = rest[k - 1];
    if (cls[last] & CL_DIGITISH != 0 or last == '.') {
        // digit- or dot-terminated host: may be IPv4 in disguise; if it
        // really is (or is invalid), the general path must handle it.
        if (isIpv4(rest[0..k])) return null;
    }
    const after = rest[k..];
    // path + query + fragment in one pass, with dot-segment validation
    var query: ?[]const u8 = null;
    var frag: ?[]const u8 = null;
    var path_text = after;
    switch (scanTailFast(after)) {
        .slow => return null,
        .plain => {},
        .frag => |fk| {
            path_text = after[0..fk];
            const f = after[fk + 1 ..];
            if (scanPlain(.frag, f) != f.len) return null;
            frag = f;
        },
        .query => |qi| {
            path_text = after[0..qi.q];
            if (qi.frag) |h| {
                query = after[qi.q + 1 .. h];
                const f = after[h + 1 ..];
                if (scanPlain(.frag, f) != f.len) return null;
                frag = f;
            } else {
                query = after[qi.q + 1 ..];
            }
        },
    }
    var w = W{ .buf = out };
    var off = Offsets{
        .scheme_end = @intCast(scheme_len - 2),
        .auth_start = @intCast(scheme_len),
        .special = true,
        .has_authority = true,
        .host_type = .domain,
        .host_start = @intCast(scheme_len),
        .host_end = @intCast(scheme_len + k),
        .path_start = @intCast(scheme_len + k),
    };
    w.buf[0..8].* = in[0..8].*; // "http://" + throwaway 8th byte for http
    w.n = scheme_len;
    if (after.len == 0) {
        w.putStr(rest[0..k]);
        w.put('/');
    } else {
        // host + path (+ "?" + query) is contiguous in the input: one copy,
        // inlined (the common tail length avoids a memcpy call entirely)
        const tail = k + path_text.len + (if (query) |q| 1 + q.len else 0);
        const t = rest[0..tail];
        const d = w.buf.ptr + w.n;
        if (t.len <= 160) {
            var ci: usize = 0;
            while (ci + 32 <= t.len) : (ci += 32) {
                d[ci..][0..32].* = t[ci..][0..32].*;
            }
            if (ci < t.len) {
                if (t.len >= 32) {
                    d[t.len - 32 ..][0..32].* = t[t.len - 32 ..][0..32].*;
                } else if (t.len >= 16) {
                    d[0..16].* = t[0..16].*;
                    d[t.len - 16 ..][0..16].* = t[t.len - 16 ..][0..16].*;
                } else {
                    for (t, 0..) |ch, j| d[j] = ch;
                }
            }
        } else {
            @memcpy(d[0..t.len], t);
        }
        w.n += t.len;
        if (query != null) off.qmark = @intCast(scheme_len + k + path_text.len);
    }
    off.path_end = @intCast(w.n);
    if (frag) |f| {
        off.hashmark = @intCast(w.n);
        w.put('#');
        w.putStr(f);
    }
    res.* = .{ .href = w.buf[0..w.n], .off = off };
    return true;
}

fn parseWithBase(input0: []const u8, base: ?*const Url, out: []u8, scratch: []u8, res: *Url) bool {
    if (builtin.mode != .ReleaseFast) {
        // caller buffer contract (see header comment); @min narrows to the
        // comptime bound's int width, hence the explicit usize casts.
        const n = input0.len;
        std.debug.assert(out.len >= 6 * n + 96 * @as(usize, @min(n, 16384)) + 2048);
        std.debug.assert(scratch.len >= n + 368 * @as(usize, @min(n, 49152)) + 512);
    }
    if (base == null) {
        if (parseFastAbsolute(input0, out, res)) |r| return r;
    }
    var in = input0;
    // trim leading/trailing C0 control or space
    while (in.len > 0 and in[0] <= 0x20) in = in[1..];
    while (in.len > 0 and in[in.len - 1] <= 0x20) in = in[0 .. in.len - 1];
    if (in.len == 0 and base == null) return false;
    const pre = prescan(in);
    // strip all \t \n \r (rare)
    if (pre.tabnl) {
        @branchHint(.unlikely);
        var n: usize = 0;
        for (in) |c| {
            if (cls[c] & CL_TABNL == 0) {
                scratch[n] = c;
                n += 1;
            }
        }
        in = scratch[0..n];
    }
    // fragment pre-prune at first '#'
    var frag: ?[]const u8 = null;
    const hash_pos = if (pre.tabnl)
        std.mem.indexOfScalar(u8, in, '#')
    else
        pre.hash;
    if (hash_pos) |h| {
        frag = in[h + 1 ..];
        in = in[0..h];
    }

    var w = W{ .buf = out };
    var off = Offsets{};
    const host_scratch = scratch[input0.len + 16 ..];

    // ---- scheme: single-word fast path for "https://" / "http://" (no base)
    const sc_https = comptime std.mem.readInt(u64, "https://", .little);
    const sc_http = comptime std.mem.readInt(u64, "http://\x00", .little);
    const sc_http_mask: u64 = 0x00FFFFFFFFFFFFFF;
    if (base == null and in.len >= 8) {
        const w8 = std.mem.readInt(u64, in[0..8], .little);
        if (w8 == sc_https) {
            @branchHint(.likely);
            w.putStr("https://");
            off.scheme_end = 6;
            off.special = true;
            off.has_authority = true;
            off.auth_start = 8;
            var rest = in[8..];
            while (rest.len > 0 and (rest[0] == '/' or rest[0] == '\\')) rest = rest[1..];
            const sinfo = SchemeInfo{ .kind = .https, .special = true, .default_port = 443 };
            if (!parseAuthorityTail(&w, &off, rest, sinfo, true, host_scratch, frag)) return false;
            res.* = .{ .href = w.buf[0..w.n], .off = off };
            return true;
        }
        if ((w8 & sc_http_mask) == sc_http) {
            w.putStr("http://");
            off.scheme_end = 5;
            off.special = true;
            off.has_authority = true;
            off.auth_start = 7;
            var rest = in[7..];
            while (rest.len > 0 and (rest[0] == '/' or rest[0] == '\\')) rest = rest[1..];
            const sinfo = SchemeInfo{ .kind = .http, .special = true, .default_port = 80 };
            if (!parseAuthorityTail(&w, &off, rest, sinfo, true, host_scratch, frag)) return false;
            res.* = .{ .href = w.buf[0..w.n], .off = off };
            return true;
        }
    }

    // ---- scheme detection (no commit)
    var scheme_idx: ?usize = null;
    if (in.len > 0 and ((in[0] | 0x20) >= 'a' and (in[0] | 0x20) <= 'z')) {
        var i: usize = 1;
        while (i < in.len) : (i += 1) {
            const c = in[i];
            const ok = ((c | 0x20) >= 'a' and (c | 0x20) <= 'z') or
                (c >= '0' and c <= '9') or c == '+' or c == '-' or c == '.';
            if (!ok) break;
        }
        if (i < in.len and in[i] == ':') scheme_idx = i;
    }

    if (scheme_idx) |si| {
        const scheme_raw = in[0..si];
        const sinfo = schemeInfo(scheme_raw);
        const rest = in[si + 1 ..];
        if (base) |b| {
            // scheme matches base's scheme: the resolvers emit the scheme
            // themselves (copied from the normalized base href).
            if (sinfo.kind == .file and b.off.is_file) {
                if (!resolveFile(&w, &off, rest, b, host_scratch, frag)) return false;
                res.* = .{ .href = w.buf[0..w.n], .off = off };
                return true;
            }
            if (sinfo.special and b.off.special and eqlICSlice(scheme_raw, b.scheme())) {
                if (!resolveTail(&w, &off, rest, b, sinfo, host_scratch, frag)) return false;
                res.* = .{ .href = w.buf[0..w.n], .off = off };
                return true;
            }
        }
        if (!parseAbsoluteRest(&w, &off, scheme_raw, rest, sinfo, host_scratch, frag)) return false;
        res.* = .{ .href = w.buf[0..w.n], .off = off };
        return true;
    }

    // ---- no scheme: need a base
    const b = base orelse return false;
    if (b.off.opaque_path) {
        // WHATWG no-scheme state: with an opaque-path base, only a bare
        // fragment input ("#...") resolves; anything else fails.
        if (in.len == 0 and frag != null) {
            const bend: usize = if (b.off.hashmark != 0) b.off.hashmark else b.href.len;
            w.putStr(b.href[0..bend]);
            off = b.off;
            off.hashmark = 0;
            writeFrag(&w, &off, frag);
            res.* = .{ .href = w.buf[0..w.n], .off = off };
            return true;
        }
        return false;
    }
    if (b.off.is_file) {
        // file: relative resolution has extra rules (drive letters, file host)
        if (!resolveFile(&w, &off, in, b, host_scratch, frag)) return false;
        res.* = .{ .href = w.buf[0..w.n], .off = off };
        return true;
    }
    if (!resolveTail(&w, &off, in, b, schemeInfo(b.scheme()), host_scratch, frag)) return false;
    res.* = .{ .href = w.buf[0..w.n], .off = off };
    return true;
}

fn eqlICSlice(a: []const u8, b: []const u8) bool {
    if (a.len != b.len) return false;
    for (a, b) |ca, cb| {
        if (lower[ca] != lower[cb]) return false;
    }
    return true;
}

inline fn isNormalizedDriveLetter(s: []const u8) bool {
    return s.len == 2 and ((s[0] | 0x20) >= 'a' and (s[0] | 0x20) <= 'z') and s[1] == ':';
}

fn writeQuery(w: *W, off: *Offsets, query: []const u8, special: bool) void {
    off.qmark = @intCast(w.n);
    w.put('?');
    const set = if (special) SET_SQUERY else SET_QUERY;
    const all_plain = if (special)
        scanPlain(.squery, query) == query.len
    else
        scanPlain(.query, query) == query.len;
    if (all_plain) w.putStr(query) else w.putEncStr(query, set);
}

fn writeFrag(w: *W, off: *Offsets, frag: ?[]const u8) void {
    if (frag) |f| {
        off.hashmark = @intCast(w.n);
        w.put('#');
        if (scanPlain(.frag, f) == f.len) w.putStr(f) else w.putEncStr(f, SET_FRAG);
    }
}

fn writeQueryFrag(w: *W, off: *Offsets, query: ?[]const u8, special: bool, frag: ?[]const u8) void {
    if (query) |q| writeQuery(w, off, q, special);
    writeFrag(w, off, frag);
}

/// Relative resolution once the scheme matches the base (or input has none).
/// `r` is the input after any matched "scheme:".
fn resolveTail(
    w: *W,
    off: *Offsets,
    r: []const u8,
    base: *const Url,
    sinfo: SchemeInfo,
    host_scratch: []u8,
    frag: ?[]const u8,
) bool {
    const special = base.off.special;
    if (r.len == 0) {
        const bend: usize = if (base.off.hashmark != 0) base.off.hashmark else base.href.len;
        w.putStr(base.href[0..bend]);
        off.* = base.off;
        off.hashmark = 0;
        writeFrag(w, off, frag);
        return true;
    }
    const c0 = r[0];
    if (c0 == '?') {
        w.putStr(base.href[0..base.off.path_end]);
        off.* = base.off;
        off.qmark = 0;
        off.hashmark = 0;
        writeQueryFrag(w, off, r[1..], special, frag);
        return true;
    }
    if (c0 == '/' or (special and c0 == '\\')) {
        if (r.len >= 2 and (r[1] == '/' or (special and r[1] == '\\'))) {
            // scheme-relative authority: "//host/path"
            w.putStr(base.href[0..base.off.scheme_end]);
            off.scheme_end = base.off.scheme_end;
            off.special = special;
            off.is_file = base.off.is_file;
            if (base.off.is_file) {
                // file: has its own host rules (empty host ok, drive letter
                // in host position becomes path, localhost elision)
                return parseFileAbsolute(w, off, r, host_scratch, frag);
            }
            var rr = r[2..];
            if (special) {
                while (rr.len > 0 and (rr[0] == '/' or rr[0] == '\\')) rr = rr[1..];
            }
            w.putStr("//");
            off.auth_start = @intCast(w.n);
            off.has_authority = true;
            return parseAuthorityTail(w, off, rr, sinfo, special, host_scratch, frag);
        }
        // absolute path: keep base through path start
        w.putStr(base.href[0..base.off.path_start]);
        const pstart = base.off.path_start;
        off.* = base.off;
        off.qmark = 0;
        off.hashmark = 0;
        const qpos = std.mem.indexOfScalar(u8, r, '?') orelse r.len;
        const query: ?[]const u8 = if (qpos < r.len) r[qpos + 1 ..] else null;
        parsePath(w, r[0..qpos], special, base.off.is_file);
        applySlashDotRule(w, pstart, base.off.has_authority);
        off.path_end = @intCast(w.n);
        writeQueryFrag(w, off, query, special, frag);
        return true;
    }
    // relative merge: base path minus its last segment + input segments
    w.putStr(base.href[0..base.off.path_start]);
    var bpath = base.pathname();
    if (!base.off.has_authority and bpath.len >= 2 and bpath[0] == '/' and bpath[1] == '.') {
        // serialized "/." artifact: the logical path starts at the second
        // slash ("/." + logical), merge against the logical path instead.
        bpath = bpath[2..];
    }
    if (std.mem.lastIndexOfScalar(u8, bpath, '/')) |k| {
        var keep = k; // exclude the slash; parsePath re-adds one per segment
        if (base.off.is_file and k == 3 and bpath[0] == '/' and isNormalizedDriveLetter(bpath[1..3])) {
            keep = 3; // "/C:" is never shortened
        }
        w.putStr(bpath[0..keep]);
    }
    const pstart = base.off.path_start;
    off.* = base.off;
    off.qmark = 0;
    off.hashmark = 0;
    const qpos = std.mem.indexOfScalar(u8, r, '?') orelse r.len;
    const query: ?[]const u8 = if (qpos < r.len) r[qpos + 1 ..] else null;
    parsePathAt(w, r[0..qpos], special, base.off.is_file, pstart);
    applySlashDotRule(w, pstart, base.off.has_authority);
    off.path_end = @intCast(w.n);
    writeQueryFrag(w, off, query, special, frag);
    return true;
}

/// "file:" input with a file: base.
fn resolveFile(
    w: *W,
    off: *Offsets,
    r: []const u8,
    base: *const Url,
    host_scratch: []u8,
    frag: ?[]const u8,
) bool {
    const sinfo = SchemeInfo{ .kind = .file, .special = true, .default_port = null };
    if (r.len > 0 and (r[0] == '/' or r[0] == '\\')) {
        if (r.len >= 2 and (r[1] == '/' or r[1] == '\\')) {
            // "//..." — host from input
            w.putStr(base.href[0..base.off.scheme_end]);
            off.scheme_end = base.off.scheme_end;
            return parseFileAbsolute(w, off, r, host_scratch, frag);
        }
        w.putStr(base.href[0..base.off.path_start]);
        off.* = base.off;
        off.qmark = 0;
        off.hashmark = 0;
        const qpos = std.mem.indexOfScalar(u8, r, '?') orelse r.len;
        const query: ?[]const u8 = if (qpos < r.len) r[qpos + 1 ..] else null;
        // WHATWG file slash state: an absolute path that does not itself lead
        // with a drive letter inherits the base's normalized drive, if any.
        const bp = base.pathname();
        const inherit_drive = bp.len >= 3 and bp[0] == '/' and
            isNormalizedDriveLetter(bp[1..3]) and
            !(r.len >= 3 and isWindowsDriveLetter(r[1..3]));
        if (inherit_drive) {
            w.put('/');
            w.put(bp[1]);
            w.put(':');
        }
        parsePathAt(w, r[0..qpos], true, true, base.off.path_start);
        off.path_end = @intCast(w.n);
        writeQueryFrag(w, off, query, true, frag);
        return true;
    }
    if (r.len >= 2 and isWindowsDriveLetter(r[0..2]) and
        (r.len == 2 or r[2] == '/' or r[2] == '\\' or r[2] == '?' or r[2] == '#'))
    {
        // drive-letter-led: new absolute path, host kept from base
        w.putStr(base.href[0..base.off.path_start]);
        off.* = base.off;
        off.qmark = 0;
        off.hashmark = 0;
        const qpos = std.mem.indexOfScalar(u8, r, '?') orelse r.len;
        const query: ?[]const u8 = if (qpos < r.len) r[qpos + 1 ..] else null;
        parsePath(w, r[0..qpos], true, true);
        off.path_end = @intCast(w.n);
        writeQueryFrag(w, off, query, true, frag);
        return true;
    }
    return resolveTail(w, off, r, base, sinfo, host_scratch, frag);
}

/// file: absolute parse (rest starts after "file:").
fn parseFileAbsolute(
    w: *W,
    off: *Offsets,
    rest0: []const u8,
    host_scratch: []u8,
    frag: ?[]const u8,
) bool {
    const rest = rest0;
    w.putStr("//");
    off.auth_start = @intCast(w.n);
    off.has_authority = true;
    off.is_file = true;
    off.special = true;
    var pathview: []const u8 = rest;
    if (rest.len >= 2 and (rest[0] == '/' or rest[0] == '\\') and
        (rest[1] == '/' or rest[1] == '\\'))
    {
        // FILE_HOST: span to next / \ ?
        const hstart_in = rest[2..];
        const hend = indexOfAnyV(hstart_in, '/', '\\', '?');
        const hostspan = hstart_in[0..hend];
        pathview = hstart_in[hend..];
        if (isWindowsDriveLetter(hostspan)) {
            // drive letter in host position -> path
            pathview = hstart_in;
        } else if (hostspan.len > 0) {
            off.host_start = @intCast(w.n);
            if (!parseHostSpecial(w, hostspan, host_scratch)) return false;
            const h = w.buf[off.host_start..w.n];
            if (std.mem.eql(u8, h, "localhost")) w.n = off.host_start;
            off.host_end = @intCast(w.n);
            off.host_type = .domain;
        }
    } else if (rest.len >= 1 and (rest[0] == '/' or rest[0] == '\\')) {
        pathview = rest[1..];
    }
    const qpos = std.mem.indexOfScalar(u8, pathview, '?') orelse pathview.len;
    const query: ?[]const u8 = if (qpos < pathview.len) pathview[qpos + 1 ..] else null;
    const pv = pathview[0..qpos];
    off.path_start = @intCast(w.n);
    if (pv.len == 0) {
        w.put('/');
    } else {
        parsePath(w, pv, true, true);
    }
    off.path_end = @intCast(w.n);
    writeQueryFrag(w, off, query, true, frag);
    return true;
}

/// Absolute URL (scheme known): dispatch on scheme kind.
fn parseAbsoluteRest(
    w: *W,
    off: *Offsets,
    scheme_raw: []const u8,
    rest0: []const u8,
    sinfo: SchemeInfo,
    host_scratch: []u8,
    frag: ?[]const u8,
) bool {
    for (scheme_raw) |c| w.put(lower[c]);
    w.put(':');
    off.scheme_end = @intCast(w.n);
    off.special = sinfo.special;
    off.is_file = sinfo.kind == .file;
    var rest = rest0;

    if (sinfo.kind == .file) {
        return parseFileAbsolute(w, off, rest, host_scratch, frag);
    }

    if (sinfo.special) {
        while (rest.len > 0 and (rest[0] == '/' or rest[0] == '\\')) rest = rest[1..];
        w.putStr("//");
        off.auth_start = @intCast(w.n);
        off.has_authority = true;
        return parseAuthorityTail(w, off, rest, sinfo, true, host_scratch, frag);
    }

    // ---- non-special
    if (rest.len >= 2 and rest[0] == '/' and rest[1] == '/') {
        w.putStr("//");
        off.auth_start = @intCast(w.n);
        off.has_authority = true;
        rest = rest[2..];
        return parseAuthorityTail(w, off, rest, sinfo, false, host_scratch, frag);
    }
    if (rest.len > 0 and rest[0] == '/') {
        const qpos = std.mem.indexOfScalar(u8, rest, '?') orelse rest.len;
        const query: ?[]const u8 = if (qpos < rest.len) rest[qpos + 1 ..] else null;
        off.path_start = @intCast(w.n);
        parsePath(w, rest[0..qpos], false, false);
        applySlashDotRule(w, off.path_start, false);
        off.path_end = @intCast(w.n);
        writeQueryFrag(w, off, query, false, frag);
        return true;
    }
    // opaque path (cannot-be-a-base)
    {
        const qpos = std.mem.indexOfScalar(u8, rest, '?') orelse rest.len;
        const query: ?[]const u8 = if (qpos < rest.len) rest[qpos + 1 ..] else null;
        const pv = rest[0..qpos];
        off.path_start = @intCast(w.n);
        off.opaque_path = true;
        if (pv.len > 0 and pv[pv.len - 1] == ' ') {
            w.putEncStr(pv[0 .. pv.len - 1], SET_C0);
            w.putStr("%20");
        } else {
            w.putEncStr(pv, SET_C0);
        }
        off.path_end = @intCast(w.n);
        writeQueryFrag(w, off, query, false, frag);
        return true;
    }
}

// host scan specialized for parseFastAbsolute: the first two 16B blocks
// inline (covers effectively every real host); longer tails defer to
// scanPlainTbl. Same result as scanPlain(.host, rest).
inline fn scanHostFast(rest: []const u8) usize {
    const n = rest.len;
    if (comptime use_tbl) {
        if (n >= 16) {
            const T = comptime tblTables(plainBoolTable(.host));
            const lo_tab: V16u8 = T.lo;
            const hi_tab: V16u8 = T.hi;
            const m0 = nonPlainMask16(lo_tab, hi_tab, rest[0..16].*);
            if (m0 != 0) return @ctz(m0) >> 2;
            if (n >= 32) {
                const m1 = nonPlainMask16(lo_tab, hi_tab, rest[16..32].*);
                if (m1 != 0) return 16 + (@ctz(m1) >> 2);
                if (n > 32) return 32 + scanPlainTbl(.host, rest[32..]);
                return n;
            }
            // 16..31 bytes: one overlapping last block
            const ml = nonPlainMask16(lo_tab, hi_tab, rest[n - 16 ..][0..16].*);
            if (ml != 0) return n - 16 + (@ctz(ml) >> 2);
            return n;
        }
    }
    return scanPlainScalar(.host, rest);
}

// combined path+query+fragment scan for inputs whose fragment was NOT
// pre-split (parseFastAbsolute). One pass, exact same accept conditions
// as scanPathFast + the squery/frag plain scans.
const TailScan = union(enum) {
    plain: void,
    frag: usize, // '#' position (no query before it)
    query: struct { q: usize, frag: ?usize }, // '?' position, optional '#' in query
    slow: usize, // needs the segment state machine / encode writer
};

const TailWalk = union(enum) { done: TailScan, query: usize, none: void };

inline fn tailWalk(after: []const u8, base: usize, m0: u64) TailWalk {
    var m = m0;
    while (m != 0) {
        const pk = base + (@ctz(m) >> 2);
        switch (pathByteCheck(after, pk)) {
            .query => return .{ .query = pk },
            .frag => return .{ .done = .{ .frag = pk } },
            .slow => return .{ .done = .{ .slow = pk } },
            .benign => m &= m - 1,
        }
    }
    return .none;
}

fn scanTailFast(after: []const u8) TailScan {
    const n = after.len;
    var i: usize = 0;
    var qpos: ?usize = null;
    path: {
        if (comptime use_tbl) {
            if (n >= 16) {
                const PT = comptime tblTables(plainBoolTable(.path));
                const plo: V16u8 = PT.lo;
                const phi: V16u8 = PT.hi;
                while (i + 32 <= n) : (i += 32) {
                    const c0: V16u8 = after[i..][0..16].*;
                    const c1: V16u8 = after[i + 16 ..][0..16].*;
                    const m0 = nonPlainMask16(plo, phi, c0);
                    const m1 = nonPlainMask16(plo, phi, c1);
                    if ((m0 | m1) != 0) {
                        switch (tailWalk(after, i, m0)) {
                            .done => |d| return d,
                            .query => |q| {
                                qpos = q;
                                break :path;
                            },
                            .none => {},
                        }
                        switch (tailWalk(after, i + 16, m1)) {
                            .done => |d| return d,
                            .query => |q| {
                                qpos = q;
                                break :path;
                            },
                            .none => {},
                        }
                    }
                }
                while (i + 16 <= n) : (i += 16) {
                    const c0: V16u8 = after[i..][0..16].*;
                    const m0 = nonPlainMask16(plo, phi, c0);
                    switch (tailWalk(after, i, m0)) {
                        .done => |d| return d,
                        .query => |q| {
                            qpos = q;
                            break :path;
                        },
                        .none => {},
                    }
                }
            }
        }
        // scalar tail (<= 15 bytes on aarch64; whole input elsewhere)
        const plainp = comptime plainBoolTable(.path);
        while (i < n) : (i += 1) {
            if (!plainp[after[i]]) {
                switch (pathByteCheck(after, i)) {
                    .query => {
                        qpos = i;
                        break :path;
                    },
                    .frag => return .{ .frag = i },
                    .slow => return .{ .slow = i },
                    .benign => {},
                }
            }
        }
    }
    const q = qpos orelse return .plain;
    // ---- query phase: only '#' may follow unencoded; anything else
    // outside the special-query plain set is slow.
    var j = q + 1;
    if (comptime use_tbl) {
        const QT = comptime tblTables(plainBoolTable(.squery));
        const qlo: V16u8 = QT.lo;
        const qhi: V16u8 = QT.hi;
        while (j + 16 <= n) : (j += 16) {
            const c0: V16u8 = after[j..][0..16].*;
            const m0 = nonPlainMask16(qlo, qhi, c0);
            if (m0 != 0) {
                const p = j + (@ctz(m0) >> 2);
                if (after[p] == '#') return .{ .query = .{ .q = q, .frag = p } };
                return .{ .slow = p };
            }
        }
    }
    const plainq = comptime plainBoolTable(.squery);
    while (j < n) : (j += 1) {
        if (!plainq[after[j]]) {
            if (after[j] == '#') return .{ .query = .{ .q = q, .frag = j } };
            return .{ .slow = j };
        }
    }
    return .{ .query = .{ .q = q, .frag = null } };
}

// shared authority+path+query+fragment tail for special and
// non-special-with-'//' URLs. `rest` starts at the authority.

const PathScanKind = enum { plain, query, frag, slow };
const PathScan = struct { kind: PathScanKind, k: usize };
const PathByte = enum { benign, query, frag, slow };

// decision for one non-path-plain byte at after[pk]: '?' ends the path;
// '#' ends it too (only reachable when the fragment was not pre-split);
// '.'/'%' are benign unless they open a dot segment ("."/".."/their %2e
// forms) at a segment start; anything else needs the segment state machine.
inline fn pathByteCheck(after: []const u8, pk: usize) PathByte {
    const c = after[pk];
    if (c == '?') return .query;
    if (c == '#') return .frag;
    if (c == '.') {
        if (pk == 0 or after[pk - 1] == '/') {
            if (pk + 1 == after.len) return .slow; // "/."
            const n1 = after[pk + 1];
            if (n1 == '/' or n1 == '%') return .slow; // "./", ".%.."
            if (n1 == '.') {
                if (pk + 2 == after.len) return .slow; // "/.."
                const n2 = after[pk + 2];
                if (n2 == '/' or n2 == '%') return .slow; // "../", "..%.."
            }
        }
        return .benign;
    }
    if (c == '%') {
        if ((pk == 0 or after[pk - 1] == '/') and pk + 2 < after.len and
            after[pk + 1] == '2' and (after[pk + 2] | 0x20) == 'e')
        {
            if (pk + 3 == after.len) return .slow;
            const n3 = after[pk + 3];
            if (n3 == '/' or n3 == '.' or n3 == '%') return .slow;
        }
        return .benign;
    }
    return .slow;
}

// walk a non-plain lane mask over after[base..]; returns the terminal
// PathScan when a non-benign byte is hit, null when all are benign.
inline fn pathWalk(after: []const u8, base: usize, m0: u64) ?PathScan {
    var m = m0;
    while (m != 0) {
        const pk = base + (@ctz(m) >> 2);
        switch (pathByteCheck(after, pk)) {
            .query => return .{ .kind = .query, .k = pk },
            .frag => return .{ .kind = .frag, .k = pk },
            .slow => return .{ .kind = .slow, .k = pk },
            .benign => m &= m - 1,
        }
    }
    return null;
}

// Fast whole-path validation for the tail-after-host paths: verifies that
// the path text is plain (nothing to percent-encode, no backslash) AND
// contains no dot segments. `.plain` means the text can be bulk-copied
// verbatim; `.query` means the same up to the '?' at k; `.slow` means the
// segment state machine must run. Single pass: benign '.'/'%' stops are
// skipped inside the current chunk's bit mask, never rescanned.
fn scanPathFast(after: []const u8) PathScan {
    const n = after.len;
    var i: usize = 0;
    if (comptime use_tbl) {
        if (n >= 16) {
            const T = comptime tblTables(plainBoolTable(.path));
            const lo_tab: V16u8 = T.lo;
            const hi_tab: V16u8 = T.hi;
            while (i + 64 <= n) : (i += 64) {
                const c0: V16u8 = after[i..][0..16].*;
                const c1: V16u8 = after[i + 16 ..][0..16].*;
                const c2: V16u8 = after[i + 32 ..][0..16].*;
                const c3: V16u8 = after[i + 48 ..][0..16].*;
                const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
                const m1 = nonPlainMask16(lo_tab, hi_tab, c1);
                const m2 = nonPlainMask16(lo_tab, hi_tab, c2);
                const m3 = nonPlainMask16(lo_tab, hi_tab, c3);
                if (((m0 | m1) | (m2 | m3)) != 0) {
                    if (pathWalk(after, i, m0)) |r| return r;
                    if (pathWalk(after, i + 16, m1)) |r| return r;
                    if (pathWalk(after, i + 32, m2)) |r| return r;
                    if (pathWalk(after, i + 48, m3)) |r| return r;
                }
            }
            while (i + 32 <= n) : (i += 32) {
                const c0: V16u8 = after[i..][0..16].*;
                const c1: V16u8 = after[i + 16 ..][0..16].*;
                const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
                const m1 = nonPlainMask16(lo_tab, hi_tab, c1);
                if ((m0 | m1) != 0) {
                    if (pathWalk(after, i, m0)) |r| return r;
                    if (pathWalk(after, i + 16, m1)) |r| return r;
                }
            }
            while (i + 16 <= n) : (i += 16) {
                const c0: V16u8 = after[i..][0..16].*;
                const m0 = nonPlainMask16(lo_tab, hi_tab, c0);
                if (pathWalk(after, i, m0)) |r| return r;
            }
        }
    }
    // scalar tail (<= 15 bytes on aarch64; whole input elsewhere)
    const plainp = comptime plainBoolTable(.path);
    while (i < n) : (i += 1) {
        if (!plainp[after[i]]) {
            switch (pathByteCheck(after, i)) {
                .query => return .{ .kind = .query, .k = i },
                .frag => return .{ .kind = .frag, .k = i },
                .slow => return .{ .kind = .slow, .k = i },
                .benign => {},
            }
        }
    }
    return .{ .kind = .plain, .k = n };
}

fn parseAuthorityTail(
    w: *W,
    off: *Offsets,
    rest: []const u8,
    sinfo: SchemeInfo,
    special: bool,
    host_scratch: []u8,
    frag: ?[]const u8,
) bool {
    // authority span: up to first '/' ( '\' if special) or '?'
    var authority: []const u8 = undefined;
    var after: []const u8 = undefined;
    if (special) {
        // fused scan: the first non-host-plain byte is either an authority
        // terminator ('/', '\\', '?') — in which case the host is already
        // validated plain — or something needing the full authority parser
        // (':' port, '@' userinfo, '[' IPv6, '%', uppercase, non-ASCII...).
        const k = scanPlain(.host, rest);
        if (k > 0 and (k == rest.len or rest[k] == '/' or rest[k] == '\\' or rest[k] == '?')) {
            @branchHint(.likely);
            authority = rest[0..k];
            after = rest[k..];
            const last = authority[authority.len - 1];
            if (cls[last] & CL_DIGITISH == 0 and last != '.') {
                off.host_type = .domain;
                // bulk common case: plain host + plain path (+ plain query);
                // the href tail is contiguous in the input, copy it in one
                // shot instead of per-component spans.
                if (after.len > 0 and after[0] == '/') {
                    const ps = scanPathFast(after);
                    if (ps.kind == .plain) {
                        off.host_start = @intCast(w.n);
                        w.putStr(rest);
                        off.host_end = @intCast(w.n - after.len);
                        off.path_start = off.host_end;
                        off.path_end = @intCast(w.n);
                        writeFrag(w, off, frag);
                        return true;
                    }
                    if (ps.kind == .query) {
                        const q = after[ps.k + 1 ..];
                        if (scanPlain(.squery, q) == q.len) {
                            off.host_start = @intCast(w.n);
                            w.putStr(rest);
                            off.host_end = @intCast(w.n - after.len);
                            off.path_start = off.host_end;
                            off.path_end = @intCast(w.n - q.len - 1);
                            off.qmark = @intCast(w.n - q.len - 1);
                            writeFrag(w, off, frag);
                            return true;
                        }
                    }
                }
                off.host_start = @intCast(w.n);
                w.putStr(authority);
                off.host_end = @intCast(w.n);
                return parseTailAfterHost(w, off, sinfo, special, after, frag);
            }
            // digit- or dot-terminated host: may be IPv4 in disguise
            off.host_start = @intCast(w.n);
            if (isIpv4(authority)) {
                if (!parseIpv4Into(w, authority)) return false;
                off.host_type = .ipv4;
            } else {
                w.putStr(authority);
                off.host_type = .domain;
            }
            off.host_end = @intCast(w.n);
            return parseTailAfterHost(w, off, sinfo, special, after, frag);
        }
        const aend = indexOfAnyV(rest, '/', '\\', '?');
        authority = rest[0..aend];
        after = rest[aend..];
    } else {
        const aend = indexOfAnyV(rest, '/', '?', null);
        authority = rest[0..aend];
        after = rest[aend..];
    }

    // ---- userinfo (split at last '@')
    var hostport = authority;
    if (std.mem.lastIndexOfScalar(u8, authority, '@')) |at_last| {
        const ui = authority[0..at_last];
        hostport = authority[at_last + 1 ..];
        if (hostport.len == 0) return false;
        // per-segment state machine (verified against ada)
        var seg_iter = std.mem.splitScalar(u8, ui, '@');
        var in_password = false;
        const ui_start = w.n;
        var colon_pos: usize = 0; // href index of the user:pass separator
        var seg_idx: usize = 0;
        while (seg_iter.next()) |seg| {
            if (seg_idx > 0) w.putStr("%40");
            if (!in_password) {
                if (std.mem.indexOfScalar(u8, seg, ':')) |colon| {
                    w.putEncStr(seg[0..colon], SET_USERINFO);
                    colon_pos = w.n;
                    w.put(':');
                    in_password = true;
                    w.putEncStr(seg[colon + 1 ..], SET_USERINFO);
                } else {
                    w.putEncStr(seg, SET_USERINFO);
                }
            } else {
                w.putEncStr(seg, SET_USERINFO);
            }
            seg_idx += 1;
        }
        // drop entirely if both user and pass empty (covers ":@" too)
        const region = w.buf[ui_start..w.n];
        const empty_ui = region.len == 0 or
            (region.len == 1 and region[0] == ':');
        if (empty_ui) {
            w.n = ui_start;
        } else {
            // ":" with empty pass but non-empty user must lose the colon;
            // empty user with pass keeps it. Region is user [':' pass...].
            if (region[region.len - 1] == ':') {
                // trailing colon == empty password -> drop it
                w.n -= 1;
                colon_pos = 0;
            }
            off.has_cred = true;
            off.cred_start = @intCast(ui_start);
            off.colon = @intCast(colon_pos);
            off.cred_end = @intCast(w.n);
            w.put('@');
        }
    }

    // ---- host : port split (first unbracketed ':')
    var hostspan = hostport;
    var portstr: []const u8 = &.{};
    var had_colon = false;
    if (hostport.len > 0 and hostport[0] == '[') {
        const close = std.mem.indexOfScalar(u8, hostport, ']') orelse {
            // unclosed bracket: whole thing is the host -> must end with ']'
            return false;
        };
        hostspan = hostport[0 .. close + 1];
        const tail = hostport[close + 1 ..];
        if (tail.len > 0) {
            if (tail[0] != ':') return false;
            portstr = tail[1..];
            had_colon = true;
        }
    } else if (std.mem.indexOfScalar(u8, hostport, ':')) |colon| {
        hostspan = hostport[0..colon];
        portstr = hostport[colon + 1 ..];
        had_colon = true;
    }

    // ---- host
    off.host_start = @intCast(w.n);
    if (hostspan.len > 0 and hostspan[0] == '[') {
        // bracketed host: IPv6 for special and non-special alike
        if (hostspan[hostspan.len - 1] != ']') return false;
        var addr: [8]u16 = undefined;
        if (!parseIpv6(hostspan[1 .. hostspan.len - 1], &addr)) return false;
        writeIpv6(w, &addr);
        off.host_type = .ipv6;
    } else if (special) {
        if (hostspan.len == 0) return false;
        // fast path: plain lowercase domain, no '%', nothing forbidden,
        // no uppercase, ASCII; watch trailing-dot / digit-ish endings
        // (those may be IPv4 in disguise).
        if (scanPlain(.host, hostspan) == hostspan.len) {
            const last = hostspan[hostspan.len - 1];
            if (cls[last] & CL_DIGITISH == 0 and last != '.') {
                w.putStr(hostspan);
                off.host_type = .domain;
            } else if (isIpv4(hostspan)) {
                if (!parseIpv4Into(w, hostspan)) return false;
                off.host_type = .ipv4;
            } else {
                w.putStr(hostspan);
                off.host_type = .domain;
            }
        } else {
            if (!parseHostSpecial(w, hostspan, host_scratch)) return false;
            off.host_type = .domain;
        }
    } else {
        // non-special opaque host: empty host with a port is invalid
        if (hostspan.len == 0 and had_colon) return false;
        if (!parseHostOpaque(w, hostspan)) return false;
        off.host_type = .opaque_host;
    }
    off.host_end = @intCast(w.n);

    // ---- port
    if (portstr.len > 0) {
        var val: u32 = 0;
        for (portstr) |c| {
            if (c < '0' or c > '9') return false;
            val = val * 10 + (c - '0');
            if (val > 65535) return false;
        }
        const elide = if (sinfo.default_port) |dp| val == dp else false;
        if (!elide) {
            off.port_start = @intCast(w.n + 1);
            w.put(':');
            w.putUint(val);
            off.port_end = @intCast(w.n);
        }
    }

    return parseTailAfterHost(w, off, sinfo, special, after, frag);
}

// path + query + fragment, once scheme/authority are done.
fn parseTailAfterHost(
    w: *W,
    off: *Offsets,
    sinfo: SchemeInfo,
    special: bool,
    after: []const u8,
    frag: ?[]const u8,
) bool {
    _ = sinfo;
    // ---- path
    // scanPathFast finds the query boundary, any byte needing the segment
    // state machine, and validates dot segments, all in one pass.
    const ps = scanPathFast(after);
    var query: ?[]const u8 = null;
    off.path_start = @intCast(w.n);
    switch (ps.kind) {
        .plain => {
            // fully plain path, no query (also covers empty `after`)
            if (after.len == 0) {
                if (special) w.put('/');
            } else {
                w.putStr(after);
            }
        },
        .query => {
            const pv = after[0..ps.k];
            query = after[ps.k + 1 ..];
            if (pv.len == 0) {
                if (special) w.put('/');
            } else {
                w.putStr(pv);
            }
        },
        .slow => {
            // dot segment, '%2e', backslash, encode-needed byte, ...
            const qpos = std.mem.indexOfScalar(u8, after, '?') orelse after.len;
            if (qpos < after.len) query = after[qpos + 1 ..];
            const pv = after[0..qpos];
            if (pv.len == 0) {
                if (special) w.put('/');
            } else {
                parsePath(w, pv, special, false);
            }
        },
        .frag => unreachable, // callers pre-split the fragment at '#'
    }
    off.path_end = @intCast(w.n);

    // ---- query / fragment
    writeQueryFrag(w, off, query, special, frag);
    return true;
}
