// idna_test.zig — differential harness for idna.zig against Ada-generated
// oracle files (ada::unicode::to_ascii ground truth).
//
//   zidnatest <input.tsv> <oracle.txt>
//
// input.tsv: one test per line, "hexinput<TAB>hex-expected-or-dash"
//            (the second field is ignored; the oracle file wins).
// oracle.txt: one line per test, hex of ada::unicode::to_ascii output,
//             or "-" when Ada returns failure.
//
// Prints each mismatch and exits non-zero when any occur.
const std = @import("std");
const idna = @import("idna.zig");

extern "c" fn open(path: [*:0]const u8, flags: c_int, ...) c_int;
extern "c" fn close(fd: c_int) c_int;
extern "c" fn mmap(addr: ?*anyopaque, len: usize, prot: c_int, flags: c_int, fd: c_int, off: i64) ?*anyopaque;
extern "c" fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern "c" fn malloc(n: usize) ?*anyopaque;

const Timespec = extern struct { tv_sec: i64, tv_nsec: i64 };
const Stat = extern struct {
    st_dev: i32,
    st_ino: u64,
    st_mode: u16,
    st_nlink: u16,
    st_uid: u32,
    st_gid: u32,
    st_rdev: i32,
    st_atimespec: Timespec,
    st_mtimespec: Timespec,
    st_ctimespec: Timespec,
    st_birthtimespec: Timespec,
    st_size: i64,
    st_blocks: i64,
    st_blksize: i32,
    st_flags: u32,
    st_gen: u32,
    st_lspare: i32,
    st_qspare: [2]i64,
};
extern "c" fn fstat(fd: c_int, st: *Stat) c_int;

fn mmapFile(path: [*:0]const u8) ?[]const u8 {
    const fd = open(path, 0);
    if (fd < 0) return null;
    defer _ = close(fd);
    var st: Stat = undefined;
    if (fstat(fd, &st) != 0) return null;
    const size: usize = @intCast(st.st_size);
    if (size == 0) return &.{};
    const mem = mmap(null, size, 1, 2, fd, 0) orelse return null;
    return @as([*]const u8, @ptrCast(mem))[0..size];
}

fn printStr(s: []const u8) void {
    _ = write(2, s.ptr, s.len);
}

fn hexVal(c: u8) ?u8 {
    if (c >= '0' and c <= '9') return c - '0';
    if (c >= 'a' and c <= 'f') return c - 'a' + 10;
    if (c >= 'A' and c <= 'F') return c - 'A' + 10;
    return null;
}

fn hexDecode(hex: []const u8, dst: []u8) ?[]const u8 {
    if (hex.len % 2 != 0) return null;
    const n = hex.len / 2;
    if (dst.len < n) return null;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        const hi = hexVal(hex[2 * i]) orelse return null;
        const lo = hexVal(hex[2 * i + 1]) orelse return null;
        dst[i] = (hi << 4) | lo;
    }
    return dst[0..n];
}

fn hexEncode(bytes: []const u8, dst: []u8) []const u8 {
    const digits = "0123456789abcdef";
    for (bytes, 0..) |b, i| {
        dst[2 * i] = digits[b >> 4];
        dst[2 * i + 1] = digits[b & 15];
    }
    return dst[0 .. 2 * bytes.len];
}

var linebuf: [1 << 20]u8 = undefined;

pub fn main(init: std.process.Init.Minimal) !void {
    const args = init.args.vector;
    if (args.len < 3) {
        printStr("usage: zidnatest <input.tsv> <oracle.txt>\n");
        return;
    }
    const tsv = mmapFile(args[1]) orelse {
        printStr("cannot open tsv\n");
        return;
    };
    const oracle = mmapFile(args[2]) orelse {
        printStr("cannot open oracle\n");
        return;
    };

    const max_in: usize = idna.max_domain_input_bytes;
    const out_cap = idna.outCapacity(max_in);
    const scratch_cap = idna.scratchCapacity(max_in);
    const out: []u8 = @as([*]u8, @ptrCast(malloc(out_cap).?))[0..out_cap];
    const scratch: []u8 = @as([*]u8, @ptrCast(malloc(scratch_cap).?))[0..scratch_cap];
    const inbuf: []u8 = @as([*]u8, @ptrCast(malloc(max_in + 64).?))[0 .. max_in + 64];
    const hexbuf: []u8 = @as([*]u8, @ptrCast(malloc(2 * out_cap + 8).?))[0 .. 2 * out_cap + 8];

    var mismatches: usize = 0;
    var total: usize = 0;
    var lineno: usize = 0;

    var tsv_it = std.mem.splitScalar(u8, tsv, '\n');
    var ora_it = std.mem.splitScalar(u8, oracle, '\n');
    while (tsv_it.next()) |raw_line| {
        const line = std.mem.trimEnd(u8, raw_line, "\r");
        if (line.len == 0) continue;
        const ora_line_raw = ora_it.next() orelse {
            printStr("oracle shorter than tsv\n");
            break;
        };
        const ora_line = std.mem.trimEnd(u8, ora_line_raw, "\r");
        lineno += 1;
        total += 1;

        const tab = std.mem.indexOfScalar(u8, line, '\t') orelse line.len;
        const input = hexDecode(line[0..tab], inbuf) orelse {
            printStr("bad hex input\n");
            continue;
        };

        const got = idna.domainToAscii(input, out, scratch);
        const ok = blk: {
            if (std.mem.eql(u8, ora_line, "-")) break :blk got == null;
            const want = hexDecode(ora_line, hexbuf) orelse break :blk false;
            if (got == null) break :blk false;
            break :blk std.mem.eql(u8, got.?, want);
        };
        if (!ok) {
            mismatches += 1;
            if (mismatches <= 25) {
                var w: usize = 0;
                const got_hex = if (got) |g| hexEncode(g, hexbuf[hexbuf.len / 2 ..]) else "-";
                const msg = std.fmt.bufPrint(linebuf[0..], "line {d}: in={s} got={s} want={s}\n", .{ lineno, line[0..tab], got_hex, ora_line }) catch continue;
                w = msg.len;
                _ = write(2, linebuf[0..w].ptr, w);
            }
        }
    }
    var sbuf: [128]u8 = undefined;
    const summary = std.fmt.bufPrint(&sbuf, "total={d} mismatches={d}\n", .{ total, mismatches }) catch unreachable;
    printStr(summary);
    if (mismatches != 0) std.process.exit(1);
}
