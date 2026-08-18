// idna.zig — Zig port of Ada's IDNA / UTS-46 implementation (src/ada_idna.cpp,
// amalgamated) plus the ada::unicode::to_ascii wrapper from src/unicode.cpp.
//
// Byte-exact behavioral parity with the C++ original:
//   - mapping.cpp            (two-level IDNA mapping table, two-pass map)
//   - normalization.cpp      (uni-algo style NFC: decompose/sort/compose)
//   - punycode.cpp           (RFC 3492 bootstrap with Ada's overflow checks)
//   - validity.cpp           (UTS-46 validity: NFC, ContextJ joiners, bidi)
//   - to_ascii.cpp           (the UTS-46 toASCII driver, max 16384 bytes)
//   - unicode_transcoding.cpp (strict UTF-8 -> UTF-32)
//   - unicode.cpp to_ascii   (percent-decode + forbidden-domain-code-point wrap)
//
// No allocation, no global state: all tables are read-only, sliced at comptime
// from the embedded blob (idna_tables.bin, little-endian). Thread-safe by
// construction.
//
// Buffer contract (n = input.len; caller sizes buffers):
//   out:     >= outCapacity(n)     = 96*n + 64 bytes
//   scratch: >= scratchCapacity(n) = 272*n + 192 bytes
// These are worst-case bounds proven from the table maxima:
//   map() expands to at most 6 code points per input byte (U+FDFA: 3B -> 18 cp),
//   canonical decomposition (NFD) expands to at most 4x the code point count,
//   punycode output is at most 4 + 11 bytes per label code point.
// The input (after percent-decoding) is rejected when longer than 16384 bytes,
// mirroring ada::idna::max_domain_input_bytes.

const std = @import("std");
const tb = @import("idna_offsets.zig");

// ------------------------------------------------------------ embedded tables

const blob_raw = @embedFile("idna_tables.bin");
const blob: *align(16) const [blob_raw.len:0]u8 = @alignCast(blob_raw);

comptime {
    std.debug.assert(blob.len == tb.uncompressed_size);
    std.debug.assert(tb.off_idna_stage1 % 2 == 0);
    std.debug.assert(tb.off_idna_stage2 % 2 == 0);
    std.debug.assert(tb.off_idna_bool_blocks % 8 == 0);
    std.debug.assert(tb.off_decomposition_block % 2 == 0);
    std.debug.assert(tb.off_decomposition_data % 4 == 0);
    std.debug.assert(tb.off_composition_block % 2 == 0);
    std.debug.assert(tb.off_composition_data % 4 == 0);
    std.debug.assert(tb.off_dir_start % 4 == 0);
    std.debug.assert(tb.off_dir_final % 4 == 0);
    std.debug.assert(tb.off_combining_flat % 4 == 0);
    std.debug.assert(tb.count_decomposition_block == tb.decomposition_block_rows * tb.decomposition_block_cols);
    std.debug.assert(tb.count_ccc_block == tb.ccc_block_rows * tb.ccc_block_cols);
    std.debug.assert(tb.count_composition_block == tb.composition_block_rows * tb.composition_block_cols);
    std.debug.assert(tb.count_dir_start == tb.count_dir_final and tb.count_dir_final == tb.count_dir_value);
}

fn tableU8(comptime off: usize, comptime count: usize) *const [count]u8 {
    return blob[off..][0..count];
}
fn tableU16(comptime off: usize, comptime count: usize) *const [count]u16 {
    comptime std.debug.assert(off % 2 == 0);
    return @ptrCast(@alignCast(blob[off..].ptr));
}
fn tableU32(comptime off: usize, comptime count: usize) *const [count]u32 {
    comptime std.debug.assert(off % 4 == 0);
    return @ptrCast(@alignCast(blob[off..].ptr));
}
fn tableU64(comptime off: usize, comptime count: usize) *const [count]u64 {
    comptime std.debug.assert(off % 8 == 0);
    return @ptrCast(@alignCast(blob[off..].ptr));
}

// Mapping
const idna_stage1 = tableU16(tb.off_idna_stage1, tb.count_idna_stage1);
const idna_stage2 = tableU16(tb.off_idna_stage2, tb.count_idna_stage2);
const idna_bool_blocks = tableU64(tb.off_idna_bool_blocks, tb.count_idna_bool_blocks);
const idna_utf8_mappings = tableU8(tb.off_idna_utf8_mappings, tb.count_idna_utf8_mappings);
// Normalization
const decomposition_index = tableU8(tb.off_decomposition_index, tb.count_decomposition_index);
const decomposition_block_flat = tableU16(tb.off_decomposition_block, tb.count_decomposition_block);
const decomposition_data = tableU32(tb.off_decomposition_data, tb.count_decomposition_data);
const ccc_index = tableU8(tb.off_ccc_index, tb.count_ccc_index);
const ccc_block_flat = tableU8(tb.off_ccc_block, tb.count_ccc_block);
const composition_index = tableU8(tb.off_composition_index, tb.count_composition_index);
const composition_block_flat = tableU16(tb.off_composition_block, tb.count_composition_block);
const composition_data = tableU32(tb.off_composition_data, tb.count_composition_data);
// Validity
const dir_start = tableU32(tb.off_dir_start, tb.count_dir_start);
const dir_final = tableU32(tb.off_dir_final, tb.count_dir_final);
const dir_value = tableU8(tb.off_dir_value, tb.count_dir_value);
const combining_flat = tableU32(tb.off_combining_flat, tb.count_combining_flat); // [start,end] pairs

// ------------------------------------------------------------- mapping table

const IDNA_BLOCK_BITS = 6;
const IDNA_BLOCK_SIZE = 64;
const IDNA_BLOCK_MASK = 63;

const IDNA_VALID: u16 = 0xFFFF;
const IDNA_DISALLOWED: u16 = 0xFFFE;
const IDNA_IGNORED: u16 = 0x0000; // index 0 = empty UTF-8 entry
const IDNA_BOOL_FLAG: u16 = 0x8000;

const IDNA_LOW_RANGE_END = 0x00033480;
const IDNA_HIGH_IGNORED_START = 0x000E0100;
const IDNA_HIGH_IGNORED_END = 0x000E01F0; // exclusive

// Mirrors idna_lookup (ada_idna.cpp:4932).
fn idnaLookup(cp: u32) u16 {
    if (cp < IDNA_LOW_RANGE_END) {
        const ref = idna_stage1[cp >> IDNA_BLOCK_BITS];
        if (ref & IDNA_BOOL_FLAG != 0) {
            const bit_idx: u32 = @as(u32, ref & ~IDNA_BOOL_FLAG) * IDNA_BLOCK_SIZE + (cp & IDNA_BLOCK_MASK);
            const is_valid = (idna_bool_blocks[bit_idx >> 6] >> @intCast(bit_idx & 63)) & 1 != 0;
            return if (is_valid) IDNA_VALID else IDNA_DISALLOWED;
        }
        return idna_stage2[@as(usize, ref) + (cp & IDNA_BLOCK_MASK)];
    }
    if (cp >= IDNA_HIGH_IGNORED_START and cp < IDNA_HIGH_IGNORED_END) {
        return IDNA_IGNORED;
    }
    return IDNA_DISALLOWED;
}

// Mirrors utf8_next (ada_idna.cpp:4953): decode one code point from the
// trusted null-terminated mapping string at `cursor` (index into
// idna_utf8_mappings), advancing the cursor.
fn utf8Next(cursor: *usize) u32 {
    const m = idna_utf8_mappings;
    const b0 = m[cursor.*];
    cursor.* += 1;
    if (b0 < 0x80) return b0;
    if (b0 < 0xE0) {
        var cp: u32 = @as(u32, b0 & 0x1F) << 6;
        cp |= m[cursor.*] & 0x3F;
        cursor.* += 1;
        return cp;
    }
    if (b0 < 0xF0) {
        var cp: u32 = @as(u32, b0 & 0x0F) << 12;
        cp |= @as(u32, m[cursor.*] & 0x3F) << 6;
        cursor.* += 1;
        cp |= m[cursor.*] & 0x3F;
        cursor.* += 1;
        return cp;
    }
    var cp: u32 = @as(u32, b0 & 0x07) << 18;
    cp |= @as(u32, m[cursor.*] & 0x3F) << 12;
    cursor.* += 1;
    cp |= @as(u32, m[cursor.*] & 0x3F) << 6;
    cursor.* += 1;
    cp |= m[cursor.*] & 0x3F;
    cursor.* += 1;
    return cp;
}

// Mirrors utf8_count_codepoints (ada_idna.cpp:4975).
fn utf8CountCodepoints(start: usize) usize {
    const m = idna_utf8_mappings;
    var n: usize = 0;
    var p = start;
    while (m[p] != 0) {
        n += 1;
        if (m[p] < 0x80) {
            p += 1;
        } else if (m[p] < 0xE0) {
            p += 2;
        } else if (m[p] < 0xF0) {
            p += 3;
        } else {
            p += 4;
        }
    }
    return n;
}

// Mirrors map() (ada_idna.cpp:5020): two-pass validate+size, then write.
// Returns the number of code points written to `out`, or null on disallowed.
fn mapInto(input: []const u32, out: []u32) ?usize {
    var out_size: usize = 0;
    for (input) |x| {
        const status = idnaLookup(x);
        if (status == IDNA_DISALLOWED) return null;
        if (status == IDNA_VALID) {
            out_size += 1;
            continue;
        }
        if (@as(usize, status) >= idna_utf8_mappings.len) return null;
        out_size += utf8CountCodepoints(status);
    }
    var w: usize = 0;
    for (input) |x| {
        const status = idnaLookup(x);
        if (status == IDNA_VALID) {
            out[w] = x;
            w += 1;
            continue;
        }
        // IGNORED or mapped (status validated in pass 1).
        var cursor: usize = status;
        while (idna_utf8_mappings[cursor] != 0) {
            out[w] = utf8Next(&cursor);
            w += 1;
        }
    }
    return out_size;
}

// ------------------------------------------------------ UTF-8 -> UTF-32 etc.

// Mirrors utf8_to_utf32 (ada_idna.cpp:32), strict validation. Returns the
// number of code points written, or 0 on error (the SWAR ASCII fast path is
// dropped; byte-at-a-time decoding is observably identical).
fn utf8ToUtf32(buf: []const u8, out: []u32) usize {
    var pos: usize = 0;
    var w: usize = 0;
    while (pos < buf.len) {
        const leading = buf[pos];
        if (leading < 0x80) {
            out[w] = leading;
            w += 1;
            pos += 1;
        } else if (leading & 0xE0 == 0xC0) {
            if (pos + 1 >= buf.len) return 0;
            if (buf[pos + 1] & 0xC0 != 0x80) return 0;
            const cp = (@as(u32, leading & 0x1F) << 6) | (buf[pos + 1] & 0x3F);
            if (cp < 0x80 or cp > 0x7FF) return 0;
            out[w] = cp;
            w += 1;
            pos += 2;
        } else if (leading & 0xF0 == 0xE0) {
            if (pos + 2 >= buf.len) return 0;
            if (buf[pos + 1] & 0xC0 != 0x80) return 0;
            if (buf[pos + 2] & 0xC0 != 0x80) return 0;
            const cp = (@as(u32, leading & 0x0F) << 12) |
                (@as(u32, buf[pos + 1] & 0x3F) << 6) | (buf[pos + 2] & 0x3F);
            if (cp < 0x800 or cp > 0xFFFF or (cp > 0xD7FF and cp < 0xE000)) return 0;
            out[w] = cp;
            w += 1;
            pos += 3;
        } else if (leading & 0xF8 == 0xF0) {
            if (pos + 3 >= buf.len) return 0;
            if (buf[pos + 1] & 0xC0 != 0x80) return 0;
            if (buf[pos + 2] & 0xC0 != 0x80) return 0;
            if (buf[pos + 3] & 0xC0 != 0x80) return 0;
            const cp = (@as(u32, leading & 0x07) << 18) |
                (@as(u32, buf[pos + 1] & 0x3F) << 12) |
                (@as(u32, buf[pos + 2] & 0x3F) << 6) | (buf[pos + 3] & 0x3F);
            if (cp <= 0xFFFF or cp > 0x10FFFF) return 0;
            out[w] = cp;
            w += 1;
            pos += 4;
        } else {
            return 0;
        }
    }
    return w;
}

// Mirrors utf32_length_from_utf8 (ada_idna.cpp:142): count of bytes that are
// not UTF-8 continuation bytes ((int8_t)c > -65).
fn utf32LengthFromUtf8(buf: []const u8) usize {
    var n: usize = 0;
    for (buf) |b| n += @intFromBool(@as(i8, @bitCast(b)) > -65);
    return n;
}

fn isAsciiBytes(view: []const u8) bool {
    for (view) |c| if (c >= 0x80) return false;
    return true;
}

fn isAsciiU32(view: []const u32) bool {
    for (view) |c| if (c >= 0x80) return false;
    return true;
}

// ------------------------------------------------------------ normalization

const hangul_sbase: u32 = 0xAC00;
const hangul_tbase: u32 = 0x11A7;
const hangul_vbase: u32 = 0x1161;
const hangul_lbase: u32 = 0x1100;
const hangul_lcount: u32 = 19;
const hangul_vcount: u32 = 21;
const hangul_tcount: u32 = 28;
const hangul_ncount: u32 = hangul_vcount * hangul_tcount;
const hangul_scount: u32 = hangul_lcount * hangul_vcount * hangul_tcount;

// O(1) row accessors with the same corrupt-blob clamp as table_store.hpp.
fn decompRow(bi: u8) []const u16 {
    const b: usize = if (bi >= tb.decomposition_block_rows) 0 else bi;
    return decomposition_block_flat[b * tb.decomposition_block_cols ..][0..tb.decomposition_block_cols];
}
fn cccRow(bi: u8) []const u8 {
    const b: usize = if (bi >= tb.ccc_block_rows) 0 else bi;
    return ccc_block_flat[b * tb.ccc_block_cols ..][0..tb.ccc_block_cols];
}
fn compRow(bi: u8) []const u16 {
    const b: usize = if (bi >= tb.composition_block_rows) 0 else bi;
    return composition_block_flat[b * tb.composition_block_cols ..][0..tb.composition_block_cols];
}

// Mirrors canonical_decomp_length (ada_idna.cpp:5132).
fn canonicalDecompLength(c: u32) usize {
    if (c >= hangul_sbase and c < hangul_sbase + hangul_scount) return 0;
    if (c >= 0x110000) return 0;
    const row = decompRow(decomposition_index[c >> 8]);
    const d0 = row[c % 256];
    const d1 = row[c % 256 + 1];
    var len: u32 = @as(u32, d1 >> 2) - (d0 >> 2);
    if (len > 0 and (d0 & 1) != 0) len = 0; // compatibility-only
    return len;
}

// Mirrors decompose() (ada_idna.cpp:5183). The C++ writes backward into the
// same (pre-grown) buffer; this writes forward into a separate buffer. The
// produced sequence is identical.
fn decomposeInto(src: []const u32, dst: []u32) usize {
    var w: usize = 0;
    for (src) |c| {
        if (c >= hangul_sbase and c < hangul_sbase + hangul_scount) {
            const s_index = c - hangul_sbase;
            dst[w] = hangul_lbase + s_index / hangul_ncount;
            w += 1;
            dst[w] = hangul_vbase + (s_index % hangul_ncount) / hangul_tcount;
            w += 1;
            if (s_index % hangul_tcount != 0) {
                dst[w] = hangul_tbase + s_index % hangul_tcount;
                w += 1;
            }
        } else if (c < 0x110000) {
            const row = decompRow(decomposition_index[c >> 8]);
            const d0 = row[c % 256];
            const d1 = row[c % 256 + 1];
            var len: u32 = @as(u32, d1 >> 2) - (d0 >> 2);
            if (len > 0 and (d0 & 1) != 0) len = 0;
            if (len > 0) {
                const base: usize = d0 >> 2;
                if (base + len > decomposition_data.len) {
                    dst[w] = c;
                    w += 1;
                } else {
                    @memcpy(dst[w .. w + len], decomposition_data[base .. base + len]);
                    w += len;
                }
            } else {
                dst[w] = c;
                w += 1;
            }
        } else {
            dst[w] = c;
            w += 1;
        }
    }
    return w;
}

// Mirrors get_ccc (ada_idna.cpp:5227).
fn getCcc(c: u32) u8 {
    if (c >= 0x110000) return 0;
    return cccRow(ccc_index[c >> 8])[c % 256];
}

// Mirrors sort_marks (ada_idna.cpp:5234): stable insertion sort by ccc.
fn sortMarks(input: []u32) void {
    var idx: usize = 1;
    while (idx < input.len) : (idx += 1) {
        const ccc = getCcc(input[idx]);
        if (ccc == 0) continue;
        const cur = input[idx];
        var back = idx;
        while (back != 0 and getCcc(input[back - 1]) > ccc) {
            input[back] = input[back - 1];
            back -= 1;
        }
        input[back] = cur;
    }
}

// Mirrors the binary search on composition_data (ada_idna.cpp:5301/5405).
// `left`/`right` are the u16 block-row bounds widened to i32, exactly as C++.
fn compositionSearch(c0: u16, c1: u16, target: u32) ?u32 {
    var left: i32 = c0;
    var right: i32 = c1;
    const data_len: i32 = @intCast(composition_data.len);
    if (left < 0 or right < left or right > data_len) return null;
    while (left + 2 < right) {
        const middle = left + (((right - left) >> 1) & ~@as(i32, 1));
        const mv = composition_data[@intCast(middle)];
        if (mv <= target) left = middle;
        if (mv >= target) right = middle;
    }
    if (left + 1 < data_len and composition_data[@intCast(left)] == target) {
        return composition_data[@intCast(left + 1)];
    }
    return null;
}

// Mirrors would_compose (ada_idna.cpp:5264).
fn wouldCompose(input: []const u32) bool {
    var input_count: usize = 0;
    while (input_count < input.len) {
        const cur = input[input_count];
        if (cur >= hangul_lbase and cur < hangul_lbase + hangul_lcount) {
            if (input_count + 1 < input.len and
                input[input_count + 1] >= hangul_vbase and
                input[input_count + 1] < hangul_vbase + hangul_vcount) return true;
            input_count += 1;
            continue;
        }
        if (cur >= hangul_sbase and cur < hangul_sbase + hangul_scount) {
            if ((cur - hangul_sbase) % hangul_tcount != 0 and
                input_count + 1 < input.len and
                input[input_count + 1] > hangul_tbase and
                input[input_count + 1] < hangul_tbase + hangul_tcount) return true;
            input_count += 1;
            continue;
        }
        if (cur < 0x110000) {
            const row = compRow(composition_index[cur >> 8]);
            const c0 = row[cur % 256];
            const c1 = row[cur % 256 + 1];
            var previous_ccc: i32 = -1;
            var j = input_count;
            while (j + 1 < input.len) : (j += 1) {
                const ccc = getCcc(input[j + 1]);
                if (c1 != c0 and previous_ccc < @as(i32, ccc)) {
                    if (compositionSearch(c0, c1, input[j + 1]) != null) return true;
                }
                if (ccc == 0) break;
                previous_ccc = ccc;
            }
            input_count = j + 1;
            continue;
        }
        input_count += 1;
    }
    return false;
}

// Mirrors is_already_nfc (ada_idna.cpp:5328).
fn isAlreadyNfc(input: []const u32) bool {
    if (input.len == 0) return true;
    for (input) |c| {
        if (canonicalDecompLength(c) == 1) return false;
    }
    var prev_ccc: u8 = 0;
    for (input) |c| {
        const ccc = getCcc(c);
        if (ccc != 0 and prev_ccc > ccc) return false;
        prev_ccc = ccc;
    }
    return !wouldCompose(input);
}

// Mirrors compose() (ada_idna.cpp:5355): in-place, returns the new length
// (composition never grows; the C++ resize at the end leaves
// composition_count elements).
fn compose(input: []u32) usize {
    var input_count: usize = 0;
    var composition_count: usize = 0;
    while (input_count < input.len) : ({
        input_count += 1;
        composition_count += 1;
    }) {
        input[composition_count] = input[input_count];
        const cur = input[input_count];
        if (cur >= hangul_lbase and cur < hangul_lbase + hangul_lcount) {
            if (input_count + 1 < input.len and
                input[input_count + 1] >= hangul_vbase and
                input[input_count + 1] < hangul_vbase + hangul_vcount)
            {
                input[composition_count] = hangul_sbase +
                    ((cur - hangul_lbase) * hangul_vcount +
                        input[input_count + 1] - hangul_vbase) * hangul_tcount;
                input_count += 1;
                if (input_count + 1 < input.len and
                    input[input_count + 1] > hangul_tbase and
                    input[input_count + 1] < hangul_tbase + hangul_tcount)
                {
                    input_count += 1;
                    input[composition_count] += input[input_count] - hangul_tbase;
                }
            }
        } else if (cur >= hangul_sbase and cur < hangul_sbase + hangul_scount) {
            if ((cur - hangul_sbase) % hangul_tcount != 0 and
                input_count + 1 < input.len and
                input[input_count + 1] > hangul_tbase and
                input[input_count + 1] < hangul_tbase + hangul_tcount)
            {
                input_count += 1;
                input[composition_count] += input[input_count] - hangul_tbase;
            }
        } else if (cur < 0x110000) {
            var row = compRow(composition_index[cur >> 8]);
            var c0 = row[cur % 256];
            var c1 = row[cur % 256 + 1];
            const initial_composition_count = composition_count;
            var previous_ccc: i32 = -1;
            while (input_count + 1 < input.len) : (input_count += 1) {
                const next = input[input_count + 1];
                const ccc = getCcc(next);
                if (c1 != c0 and previous_ccc < @as(i32, ccc)) {
                    if (compositionSearch(c0, c1, next)) |composed| {
                        input[initial_composition_count] = composed;
                        row = compRow(composition_index[composed >> 8]);
                        c0 = row[composed % 256];
                        c1 = row[composed % 256 + 1];
                        continue;
                    }
                }
                if (ccc == 0) break;
                previous_ccc = ccc;
                composition_count += 1;
                input[composition_count] = next;
            }
        }
    }
    return composition_count;
}

// Mirrors normalize() (ada_idna.cpp:5442). The result is written to `dst`
// (which must not alias `src`) and its length returned; when `src` is already
// NFC the C++ leaves it untouched — we still copy it to `dst` so callers can
// uniformly use the returned slice (identical contents).
fn normalizeInto(src: []const u32, dst: []u32) usize {
    if (isAlreadyNfc(src)) {
        @memcpy(dst[0..src.len], src);
        return src.len;
    }
    const dlen = decomposeInto(src, dst);
    sortMarks(dst[0..dlen]);
    return compose(dst[0..dlen]);
}

// ---------------------------------------------------------------- punycode

const pc_base: i32 = 36;
const pc_tmin: i32 = 1;
const pc_tmax: i32 = 26;
const pc_skew: i32 = 38;
const pc_damp: i32 = 700;
const pc_initial_bias: i32 = 72;
const pc_initial_n: u32 = 128;

fn charToDigitValue(c: u8) i32 {
    if (c >= 'a' and c <= 'z') return c - 'a';
    if (c >= '0' and c <= '9') return c - '0' + 26;
    return -1;
}

fn digitToChar(digit: i32) u8 {
    return @intCast(if (digit < 26) digit + 97 else digit + 22);
}

fn adapt(d_in: i32, n: i32, firsttime: bool) i32 {
    var d = d_in;
    d = if (firsttime) @divTrunc(d, pc_damp) else @divTrunc(d, 2);
    d += @divTrunc(d, n);
    var k: i32 = 0;
    while (d > @divTrunc((pc_base - pc_tmin) * pc_tmax, 2)) {
        d = @divTrunc(d, pc_base - pc_tmin);
        k += pc_base;
    }
    return k + @divTrunc((pc_base - pc_tmin + 1) * d, d + pc_skew);
}

// Mirrors punycode_to_utf32 (ada_idna.cpp:5517), including the double-encoded
// ACE ("xn--") rejection. Returns decoded length or null on failure.
fn punycodeToUtf32(input: []const u8, out: []u32) ?usize {
    var written_out: i32 = 0;
    var n: u32 = pc_initial_n;
    var i: i32 = 0;
    var bias: i32 = pc_initial_bias;
    var rest = input;
    if (std.mem.lastIndexOfScalar(u8, rest, '-')) |end_of_ascii| {
        for (rest[0..end_of_ascii]) |c| {
            if (c >= 0x80) return null;
            out[@intCast(written_out)] = c;
            written_out += 1;
        }
        rest = rest[end_of_ascii + 1 ..];
    }
    while (rest.len > 0) {
        const oldi = i;
        var w: i32 = 1;
        var k: i32 = pc_base;
        while (true) : (k += pc_base) {
            if (rest.len == 0) return null;
            const code_point = rest[0];
            rest = rest[1..];
            const digit = charToDigitValue(code_point);
            if (digit < 0) return null;
            if (digit > @divTrunc(@as(i32, 0x7fffffff) - i, w)) return null;
            i = i + digit * w;
            const t: i32 = if (k <= bias) pc_tmin else if (k >= bias + pc_tmax) pc_tmax else k - bias;
            if (digit < t) break;
            if (w > @divTrunc(@as(i32, 0x7fffffff), pc_base - t)) return null;
            w = w * (pc_base - t);
        }
        bias = adapt(i - oldi, written_out + 1, oldi == 0);
        if (@divTrunc(i, written_out + 1) > @as(i32, @intCast(@as(u32, 0x7fffffff) - n))) return null;
        n = n + @as(u32, @intCast(@divTrunc(i, written_out + 1)));
        i = @rem(i, written_out + 1); // i >= 0, so rem == C++ %
        if (n < 0x80) return null;
        // Insert n at position i (std::insert semantics).
        const pos: usize = @intCast(i);
        var j: usize = @intCast(written_out);
        while (j > pos) : (j -= 1) out[j] = out[j - 1];
        out[pos] = n;
        written_out += 1;
        i += 1;
    }
    const out_len: usize = @intCast(written_out);
    // https://github.com/whatwg/url/issues/803
    if (out_len >= 4 and out[0] == 'x' and out[1] == 'n' and out[2] == '-' and out[3] == '-') {
        return null;
    }
    return out_len;
}

// Byte output cursor (bounds-checked; callers size the buffer per contract).
const ByteBuf = struct {
    buf: []u8,
    len: usize = 0,

    fn push(self: *ByteBuf, b: u8) void {
        self.buf[self.len] = b;
        self.len += 1;
    }
};

// Mirrors utf32_to_punycode (ada_idna.cpp:5661). Appends to `out`.
fn utf32ToPunycode(input: []const u32, out: *ByteBuf) bool {
    var n: u32 = pc_initial_n;
    var d: i32 = 0;
    var bias: i32 = pc_initial_bias;
    var h: usize = 0;
    for (input) |c| {
        if (c < 0x80) {
            h += 1;
            out.push(@intCast(c));
        }
        if (c > 0x10FFFF or (c >= 0xD800 and c < 0xE000)) return false;
    }
    const b = h;
    if (b > 0) out.push('-');
    while (h < input.len) {
        var m: u32 = 0x10FFFF;
        for (input) |cp| {
            if (cp >= n and cp < m) m = cp;
        }
        // C++: (m - n) > (0x7fffffff - d) / (h + 1), all non-negative.
        if (@as(u64, m - n) > @divTrunc(@as(u64, 0x7fffffff) - @as(u64, @intCast(d)), h + 1)) {
            return false;
        }
        d = d + @as(i32, @intCast((m - n) * (h + 1)));
        n = m;
        for (input) |c| {
            if (c < n) {
                if (d == 0x7fffffff) return false;
                d += 1;
            }
            if (c == n) {
                var q = d;
                var k: i32 = pc_base;
                while (true) : (k += pc_base) {
                    const t: i32 = if (k <= bias) pc_tmin else if (k >= bias + pc_tmax) pc_tmax else k - bias;
                    if (q < t) break;
                    out.push(digitToChar(t + @rem(q - t, pc_base - t)));
                    q = @divTrunc(q - t, pc_base - t);
                }
                out.push(digitToChar(q));
                bias = adapt(d, @intCast(h + 1), h == b);
                d = 0;
                h += 1;
            }
        }
        d += 1;
        n += 1;
    }
    return true;
}

// ---------------------------------------------------------------- validity

// Mirrors the direction enum (ada_idna.cpp:5732); values are significant
// (shift masks, dir_value table entries).
const Direction = enum(u8) {
    none,
    bn,
    cs,
    es,
    on,
    en,
    l,
    r,
    nsm,
    al,
    an,
    et,
    ws,
    rlo,
    lro,
    pdf,
    rle,
    rli,
    fsi,
    pdi,
    lri,
    b,
    s,
    lre,
};

// Mirrors find_direction (ada_idna.cpp:5765): binary search on dir_final.
fn findDirection(code_point: u32) Direction {
    var lo: usize = 0;
    var hi: usize = dir_final.len;
    while (lo < hi) {
        const mid = lo + (hi - lo) / 2;
        if (dir_final[mid] < code_point) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if (lo == dir_final.len) return .none;
    return if (code_point >= dir_start[lo]) @enumFromInt(dir_value[lo]) else .none;
}

// Mirrors find_last_not_of_nsm (ada_idna.cpp:5783).
fn findLastNotOfNsm(label: []const u32) ?usize {
    var i = label.len;
    while (i > 0) {
        i -= 1;
        if (findDirection(label[i]) != .nsm) return i;
    }
    return null;
}

// Mirrors is_rtl_label (ada_idna.cpp:5793).
fn isRtlLabel(label: []const u32) bool {
    const mask = (@as(u32, 1) << @intFromEnum(Direction.r)) |
        (@as(u32, 1) << @intFromEnum(Direction.al)) |
        (@as(u32, 1) << @intFromEnum(Direction.an));
    var directions: u32 = 0;
    for (label) |c| {
        directions |= @as(u32, 1) << @as(u5, @intCast(@intFromEnum(findDirection(c))));
    }
    return directions & mask != 0;
}

fn binarySearchU32(haystack: []const u32, needle: u32) bool {
    var lo: usize = 0;
    var hi: usize = haystack.len;
    while (lo < hi) {
        const mid = lo + (hi - lo) / 2;
        if (haystack[mid] < needle) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    return lo < haystack.len and haystack[lo] == needle;
}

// ContextJ tables (ada_idna.cpp:5852-5908), sorted for binary search.
const virama_table = [_]u32{
    0x94d,   0x9cd,   0xa4d,   0xacd,   0xb4d,   0xbcd,   0xc4d,   0xccd,   0xd3b,   0xd3c,
    0xd4d,   0xdca,   0xe3a,   0xeba,   0xf84,   0x1039,  0x103a,  0x1714,  0x1734,  0x17d2,
    0x1a60,  0x1b44,  0x1baa,  0x1bab,  0x1bf2,  0x1bf3,  0x2d7f,  0xa806,  0xa82c,  0xa8c4,
    0xa953,  0xa9c0,  0xaaf6,  0xabed,  0x10a3f, 0x11046, 0x1107f, 0x110b9, 0x11133, 0x11134,
    0x111c0, 0x11235, 0x112ea, 0x1134d, 0x11442, 0x114c2, 0x115bf, 0x1163f, 0x116b6, 0x1172b,
    0x11839, 0x1193d, 0x1193e, 0x119e0, 0x11a34, 0x11a47, 0x11a99, 0x11c3f, 0x11d44, 0x11d45,
    0x11d97,
};
const r_table = [_]u32{
    0x622, 0x623, 0x624, 0x625, 0x627, 0x629, 0x62f, 0x630, 0x631, 0x632,
    0x648, 0x671, 0x672, 0x673, 0x675, 0x676, 0x677, 0x688, 0x689, 0x68a,
    0x68b, 0x68c, 0x68d, 0x68e, 0x68f, 0x690, 0x691, 0x692, 0x693, 0x694,
    0x695, 0x696, 0x697, 0x698, 0x699, 0x6c0, 0x6c3, 0x6c4, 0x6c5, 0x6c6,
    0x6c7, 0x6c8, 0x6c9, 0x6ca, 0x6cb, 0x6cd, 0x6cf, 0x6d2, 0x6d3, 0x6d5,
    0x6ee, 0x6ef, 0x710, 0x715, 0x716, 0x717, 0x718, 0x719, 0x71e, 0x728,
    0x72a, 0x72c, 0x72f, 0x74d, 0x759, 0x75a, 0x75b, 0x854, 0x8aa, 0x8ab,
    0x8ac,
};
const l_table = [_]u32{0xa872};
const d_table = [_]u32{
    0x620,  0x626,  0x628,  0x62a,  0x62b,  0x62c,  0x62d,  0x62e,  0x633,  0x634,
    0x635,  0x636,  0x637,  0x638,  0x639,  0x63a,  0x63b,  0x63c,  0x63d,  0x63e,
    0x63f,  0x641,  0x642,  0x643,  0x644,  0x645,  0x646,  0x647,  0x649,  0x64a,
    0x66e,  0x66f,  0x678,  0x679,  0x67a,  0x67b,  0x67c,  0x67d,  0x67e,  0x67f,
    0x680,  0x681,  0x682,  0x683,  0x684,  0x685,  0x686,  0x687,  0x69a,  0x69b,
    0x69c,  0x69d,  0x69e,  0x69f,  0x6a0,  0x6a1,  0x6a2,  0x6a3,  0x6a4,  0x6a5,
    0x6a6,  0x6a7,  0x6a8,  0x6a9,  0x6aa,  0x6ab,  0x6ac,  0x6ad,  0x6ae,  0x6af,
    0x6b0,  0x6b1,  0x6b2,  0x6b3,  0x6b4,  0x6b5,  0x6b6,  0x6b7,  0x6b8,  0x6b9,
    0x6ba,  0x6bb,  0x6bc,  0x6bd,  0x6be,  0x6bf,  0x6c1,  0x6c2,  0x6cc,  0x6ce,
    0x6d0,  0x6d1,  0x6fa,  0x6fb,  0x6fc,  0x6ff,  0x712,  0x713,  0x714,  0x71a,
    0x71b,  0x71c,  0x71d,  0x71f,  0x720,  0x721,  0x722,  0x723,  0x724,  0x725,
    0x726,  0x727,  0x729,  0x72b,  0x72d,  0x72e,  0x74e,  0x74f,  0x750,  0x751,
    0x752,  0x753,  0x754,  0x755,  0x756,  0x757,  0x758,  0x75c,  0x75d,  0x75e,
    0x75f,  0x760,  0x761,  0x762,  0x763,  0x764,  0x765,  0x766,  0x850,  0x851,
    0x852,  0x853,  0x855,  0x8a0,  0x8a2,  0x8a3,  0x8a4,  0x8a5,  0x8a6,  0x8a7,
    0x8a8,  0x8a9,  0x1807, 0x1820, 0x1821, 0x1822, 0x1823, 0x1824, 0x1825, 0x1826,
    0x1827, 0x1828, 0x1829, 0x182a, 0x182b, 0x182c, 0x182d, 0x182e, 0x182f, 0x1830,
    0x1831, 0x1832, 0x1833, 0x1834, 0x1835, 0x1836, 0x1837, 0x1838, 0x1839, 0x183a,
    0x183b, 0x183c, 0x183d, 0x183e, 0x183f, 0x1840, 0x1841, 0x1842, 0x1843, 0x1844,
    0x1845, 0x1846, 0x1847, 0x1848, 0x1849, 0x184a, 0x184b, 0x184c, 0x184d, 0x184e,
    0x184f, 0x1850, 0x1851, 0x1852, 0x1853, 0x1854, 0x1855, 0x1856, 0x1857, 0x1858,
    0x1859, 0x185a, 0x185b, 0x185c, 0x185d, 0x185e, 0x185f, 0x1860, 0x1861, 0x1862,
    0x1863, 0x1864, 0x1865, 0x1866, 0x1867, 0x1868, 0x1869, 0x186a, 0x186b, 0x186c,
    0x186d, 0x186e, 0x186f, 0x1870, 0x1871, 0x1872, 0x1873, 0x1874, 0x1875, 0x1876,
    0x1877, 0x1887, 0x1888, 0x1889, 0x188a, 0x188b, 0x188c, 0x188d, 0x188e, 0x188f,
    0x1890, 0x1891, 0x1892, 0x1893, 0x1894, 0x1895, 0x1896, 0x1897, 0x1898, 0x1899,
    0x189a, 0x189b, 0x189c, 0x189d, 0x189e, 0x189f, 0x18a0, 0x18a1, 0x18a2, 0x18a3,
    0x18a4, 0x18a5, 0x18a6, 0x18a7, 0x18a8, 0x18aa, 0xa840, 0xa841, 0xa842, 0xa843,
    0xa844, 0xa845, 0xa846, 0xa847, 0xa848, 0xa849, 0xa84a, 0xa84b, 0xa84c, 0xa84d,
    0xa84e, 0xa84f, 0xa850, 0xa851, 0xa852, 0xa853, 0xa854, 0xa855, 0xa856, 0xa857,
    0xa858, 0xa859, 0xa85a, 0xa85b, 0xa85c, 0xa85d, 0xa85e, 0xa85f, 0xa860, 0xa861,
    0xa862, 0xa863, 0xa864, 0xa865, 0xa866, 0xa867, 0xa868, 0xa869, 0xa86a, 0xa86b,
    0xa86c, 0xa86d, 0xa86e, 0xa86f, 0xa870, 0xa871,
};

// Mirrors is_label_valid (ada_idna.cpp:5804), including the early `return true`
// when a joiner follows a virama.
fn isLabelValid(label: []const u32) bool {
    if (label.len == 0) return true;

    // The label must not begin with a combining mark: lower_bound on the
    // [start, end] combining ranges, keyed by range end.
    const front = label[0];
    const range_count = combining_flat.len / 2;
    var lo: usize = 0;
    var hi: usize = range_count;
    while (lo < hi) {
        const mid = lo + (hi - lo) / 2;
        if (combining_flat[mid * 2 + 1] < front) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if (lo < range_count and front >= combining_flat[lo * 2]) return false;

    // ContextJ joiner rules.
    for (label, 0..) |c, i| {
        if (c == 0x200c) {
            if (i > 0 and binarySearchU32(&virama_table, label[i - 1])) return true;
            if (i == 0 or i + 1 >= label.len) return false;
            var has_l_or_d = false;
            for (label[0..i]) |code| {
                if (binarySearchU32(&l_table, code) or binarySearchU32(&d_table, code)) {
                    has_l_or_d = true;
                    break;
                }
            }
            if (!has_l_or_d) return false;
            for (label[i + 1 ..]) |code| {
                if (binarySearchU32(&r_table, code) or binarySearchU32(&d_table, code)) {
                    return true;
                }
            }
            return false;
        } else if (c == 0x200d) {
            if (i > 0 and binarySearchU32(&virama_table, label[i - 1])) return true;
            return false;
        }
    }

    // CheckBidi (RFC 5893 section 2).
    const last_non_nsm_char = findLastNotOfNsm(label) orelse return false;

    if (isRtlLabel(label)) {
        if (findDirection(label[0]) == .l) {
            // Evaluate as LTR.
            for (label[0 .. last_non_nsm_char + 1]) |c| {
                const d = findDirection(c);
                if (!(d == .l or d == .en or d == .es or d == .cs or d == .et or
                    d == .on or d == .bn or d == .nsm)) return false;
            }
            const last_dir = findDirection(label[last_non_nsm_char]);
            if (!(last_dir == .l or last_dir == .en)) return false;
            return true;
        } else {
            // Evaluate as RTL; first character must be R or AL.
            const first_dir = findDirection(label[0]);
            if (first_dir != .r and first_dir != .al) return false;

            var has_an = false;
            var has_en = false;
            for (0..last_non_nsm_char + 1) |i| {
                const d = findDirection(label[i]);
                // If an EN is present, no AN may be present, and vice versa.
                if (d == .en) {
                    if (has_an) return false;
                    has_en = true;
                }
                if (d == .an) {
                    if (has_en) return false;
                    has_an = true;
                }
                if (!(d == .r or d == .al or d == .an or d == .en or d == .es or
                    d == .cs or d == .et or d == .on or d == .bn or d == .nsm))
                {
                    return false;
                }
                if (i == last_non_nsm_char and
                    !(d == .r or d == .al or d == .an or d == .en)) return false;
            }
            return true;
        }
    }

    return true;
}

// --------------------------------------------------------------- to_ascii

pub const max_domain_input_bytes = 16384;

// Mirrors is_forbidden_domain_code_point (src/unicode.cpp:267): bytes
// 0x00-0x20, 0x7F-0xFF, and # / : < > ? @ [ \ ] ^ | %.
const forbidden_domain_table: [256]bool = blk: {
    var t = [_]bool{false} ** 256;
    for (0..33) |c| t[c] = true;
    for (127..256) |c| t[c] = true;
    for ("#/:<>?@[\\]^|%") |c| t[c] = true;
    break :blk t;
};

fn containsForbiddenDomainCodePoint(s: []const u8) bool {
    for (s) |c| if (forbidden_domain_table[c]) return true;
    return false;
}

// Lowercase ASCII in place. Mirrors ascii_map (ada_idna.cpp:4993) — the SWAR
// kernel is replaced by a scalar loop; on its only reachable inputs (pure
// ASCII strings) the result is identical.
fn asciiMap(input: []u8) void {
    for (input) |*c| {
        if (c.* >= 'A' and c.* <= 'Z') c.* += 32;
    }
}

fn hexVal(c: u8) ?u8 {
    if (c >= '0' and c <= '9') return c - '0';
    if (c >= 'a' and c <= 'f') return c - 'a' + 10;
    if (c >= 'A' and c <= 'F') return c - 'A' + 10;
    return null;
}

// Mirrors percent_decode (src/unicode.cpp:458): lenient — an invalid or
// truncated %XX sequence leaves the '%' literal and scanning continues.
fn percentDecode(input: []const u8, first_percent: usize, dst: []u8) []const u8 {
    @memcpy(dst[0..first_percent], input[0..first_percent]);
    var d = first_percent;
    var p = first_percent;
    while (p < input.len) {
        if (input[p] == '%') {
            while (p + 2 < input.len and input[p] == '%') {
                const h1 = hexVal(input[p + 1]) orelse break;
                const h2 = hexVal(input[p + 2]) orelse break;
                dst[d] = h1 * 16 + h2;
                d += 1;
                p += 3;
            }
            if (p < input.len and input[p] == '%') {
                dst[d] = input[p];
                d += 1;
                p += 1;
            }
        } else {
            var q = p;
            while (q < input.len and input[q] != '%') q += 1;
            @memcpy(dst[d .. d + (q - p)], input[p..q]);
            d += q - p;
            p = q;
        }
    }
    return dst[0..d];
}

// True if label begins with "xn--" (already lowercased by mapping).
fn isAcePrefix(label: []const u32) bool {
    return label.len >= 4 and label[0] == 'x' and label[1] == 'n' and
        label[2] == '-' and label[3] == '-';
}

// Carved views over the caller's scratch buffer.
const Buffers = struct {
    w_in: []u32, // UTF-32 form of the (decoded) input; cap n
    mapped: []u32, // map() output; cap 6n
    nfd: []u32, // normalize(mapped) scratch/result; cap 24n
    decoded: []u32, // ACE punycode decode; cap 6n
    postmap: []u32, // map(decoded) (length forced equal to decoded); cap 6n
    nfd2: []u32, // normalize(postmap) scratch/result; cap 24n
    pd: []u8, // percent-decoded input; cap n
};

// Minimum out buffer size for toAscii / domainToAscii.
pub fn outCapacity(input_len: usize) usize {
    return 96 * input_len + 64;
}

// Minimum scratch buffer size for toAscii / domainToAscii.
pub fn scratchCapacity(input_len: usize) usize {
    return 272 * input_len + 192;
}

fn carveBuffers(scratch: []u8, n: usize) Buffers {
    const addr = @intFromPtr(scratch.ptr);
    const skip: usize = @intCast((@as(usize, 4) - (addr & 3)) & 3);
    const base: [*]u8 = scratch.ptr + skip;
    var fba: [*]u32 = @ptrCast(@alignCast(base));
    var rest = scratch[skip + 4 * (67 * n + 40) ..];

    const w_in = fba[0..n];
    fba += n;
    const mapped = fba[0 .. 6 * n + 8];
    fba += 6 * n + 8;
    const nfd = fba[0 .. 24 * n + 8];
    fba += 24 * n + 8;
    const decoded = fba[0 .. 6 * n + 8];
    fba += 6 * n + 8;
    const postmap = fba[0 .. 6 * n + 8];
    fba += 6 * n + 8;
    const nfd2 = fba[0 .. 24 * n + 8];
    fba += 24 * n + 8;

    const pd = rest[0 .. n + 8];
    return .{
        .w_in = w_in,
        .mapped = mapped,
        .nfd = nfd,
        .decoded = decoded,
        .postmap = postmap,
        .nfd2 = nfd2,
        .pd = pd,
    };
}

// Mirrors ada::idna::to_ascii (ada_idna.cpp:6208). Raw UTS-46 toASCII: no
// percent-decoding and no forbidden-code-point check. Returns the ASCII domain
// inside `out` (possibly an empty slice), or null on failure.
//
// Buffer contract: out.len >= outCapacity(input.len),
// scratch.len >= scratchCapacity(input.len).
pub fn toAscii(input: []const u8, out: []u8, scratch: []u8) ?[]const u8 {
    if (input.len > max_domain_input_bytes) return null;
    const bufs = carveBuffers(scratch, input.len);

    if (isAsciiBytes(input)) {
        // from_ascii_to_ascii: copy + lowercase, no further validation.
        const res = out[0..input.len];
        @memcpy(res, input);
        asciiMap(res);
        return res;
    }

    const utf32_length = utf32LengthFromUtf8(input);
    if (utf32_length == 0 and input.len != 0) return null;
    const actual_utf32_length = utf8ToUtf32(input, bufs.w_in);
    if (actual_utf32_length == 0 or actual_utf32_length != utf32_length) return null;
    const working = bufs.w_in[0..actual_utf32_length];

    const mapped_len = mapInto(working, bufs.mapped) orelse return null;
    var mapped = bufs.mapped[0..mapped_len];

    // Skip NFC when already normalized (ASCII is a fast subset of this check).
    if (!isAsciiU32(mapped) and !isAlreadyNfc(mapped)) {
        const f = normalizeInto(mapped, bufs.nfd);
        mapped = bufs.nfd[0..f];
    }

    var o = ByteBuf{ .buf = out };
    var p: usize = 0;
    const end = mapped.len;
    while (p < end) {
        const label_begin = p;
        while (p < end and mapped[p] != '.') p += 1;
        const label = mapped[label_begin..p];
        const is_last_label = p == end;
        if (p < end) p += 1; // skip dot

        if (label.len == 0) {
            // empty label
        } else if (isAcePrefix(label)) {
            for (label) |c| {
                if (c >= 0x80) return null;
            }
            for (label) |c| o.push(@intCast(c));
            const segment = o.buf[o.len - label.len + 4 .. o.len];
            const decoded_len = punycodeToUtf32(segment, bufs.decoded) orelse return null;
            const decoded = bufs.decoded[0..decoded_len];
            if (isAsciiU32(decoded)) return null;
            // Mapping must be stable; NFC must not change the mapped form.
            const pm_len = mapInto(decoded, bufs.postmap) orelse return null;
            const postmap = bufs.postmap[0..pm_len];
            if (!std.mem.eql(u32, postmap, decoded)) return null;
            if (!isAsciiU32(postmap) and !isAlreadyNfc(postmap)) {
                const f = normalizeInto(postmap, bufs.nfd2);
                if (!std.mem.eql(u32, bufs.nfd2[0..f], decoded)) return null;
            }
            if (postmap.len == 0 or !isLabelValid(postmap)) return null;
        } else if (isAsciiU32(label)) {
            for (label) |c| o.push(@intCast(c));
        } else {
            if (!isLabelValid(label)) return null;
            o.push('x');
            o.push('n');
            o.push('-');
            o.push('-');
            if (!utf32ToPunycode(label, &o)) return null;
        }
        if (!is_last_label) o.push('.');
    }
    return o.buf[0..o.len];
}

// Mirrors ada::unicode::to_ascii (src/unicode.cpp:654): percent-decode the
// input if it contains '%', run UTS-46 toASCII, reject an empty result and
// results containing forbidden domain code points. Returns the ASCII domain
// inside `out`, or null on failure.
//
// Buffer contract (n = input.len, i.e. the *encoded* length):
//   out.len >= outCapacity(n), scratch.len >= scratchCapacity(n).
pub fn domainToAscii(input: []const u8, out: []u8, scratch: []u8) ?[]const u8 {
    var real_input = input;
    if (std.mem.indexOfScalar(u8, input, '%')) |first_percent| {
        const bufs = carveBuffers(scratch, input.len);
        real_input = percentDecode(input, first_percent, bufs.pd);
    }
    const res = toAscii(real_input, out, scratch) orelse return null;
    if (res.len == 0) return null;
    if (containsForbiddenDomainCodePoint(res)) return null;
    return res;
}
