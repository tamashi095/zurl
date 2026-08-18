// zig-url bench + dump harness.
//   zurl bench <file> [--alloc] [--rounds N]  -> ns/url, GB/s (best of N passes)
//   zurl dump <file>                          -> one href or "INVALID" per line
const std = @import("std");
const url = @import("url.zig");

const Timespec = extern struct { tv_sec: i64, tv_nsec: i64 };
extern "c" fn clock_gettime(clk: c_int, ts: *Timespec) c_int;
extern "c" fn open(path: [*:0]const u8, flags: c_int, ...) c_int;
extern "c" fn close(fd: c_int) c_int;
extern "c" fn mmap(addr: ?*anyopaque, len: usize, prot: c_int, flags: c_int, fd: c_int, off: i64) ?*anyopaque;
extern "c" fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern "c" fn malloc(n: usize) ?*anyopaque;
extern "c" fn free(p: ?*anyopaque) void;
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

fn nowNs() u64 {
    var ts: Timespec = undefined;
    _ = clock_gettime(4, &ts); // CLOCK_MONOTONIC_RAW
    return @as(u64, @intCast(ts.tv_sec)) * 1_000_000_000 + @as(u64, @intCast(ts.tv_nsec));
}

inline fn isSpace(c: u8) bool {
    return c == ' ' or (c >= 9 and c <= 13);
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

fn mmapFile(path: [*:0]const u8) ?[]const u8 {
    const fd = open(path, 0);
    if (fd < 0) return null;
    defer _ = close(fd);
    var st: Stat = undefined;
    if (fstat(fd, &st) != 0) return null;
    const size: usize = @intCast(st.st_size);
    if (size == 0) return &.{};
    const mem = mmap(null, size, 1, 2, fd, 0) orelse return null; // PROT_READ, MAP_PRIVATE
    return @as([*]const u8, @ptrCast(mem))[0..size];
}

var outbuf: [8 << 20]u8 = undefined;
var outlen: usize = 0;
fn flushOut() void {
    if (outlen > 0) {
        _ = write(1, outbuf[0..outlen].ptr, outlen);
        outlen = 0;
    }
}
fn emit(s: []const u8) void {
    if (outlen + s.len + 1 > outbuf.len) flushOut();
    @memcpy(outbuf[outlen .. outlen + s.len], s);
    outlen += s.len;
    outbuf[outlen] = '\n';
    outlen += 1;
}
fn printStr(s: []const u8) void {
    _ = write(2, s.ptr, s.len);
}

pub fn main(init: std.process.Init.Minimal) !void {
    const args = init.args.vector;
    if (args.len < 2) {
        printStr("usage: zurl bench <file> [--alloc] [--rounds N] | zurl dump <file>\n");
        return;
    }
    const mode = std.mem.sliceTo(args[1], 0);
    const path: [*:0]const u8 = if (args.len > 2) args[2] else "build-bench/_deps/url-dataset-src/out.txt";
    var use_alloc = false;
    var rounds: u32 = 0;
    var ai: usize = 3;
    while (ai < args.len) : (ai += 1) {
        const a = std.mem.sliceTo(args[ai], 0);
        if (std.mem.eql(u8, a, "--alloc")) {
            use_alloc = true;
        } else if (std.mem.eql(u8, a, "--rounds") and ai + 1 < args.len) {
            ai += 1;
            rounds = @intCast(try std.fmt.parseInt(u32, std.mem.sliceTo(args[ai], 0), 10));
        }
    }

    const data = mmapFile(path) orelse {
        printStr("cannot open file\n");
        return;
    };

    // split into lines; dump/bench trim isspace like the C++ harness, wpt
    // keeps raw lines (hex TSV may carry a leading tab = empty base)
    const wpt_mode = std.mem.eql(u8, mode, "wpt");
    const max_lines = data.len / 2 + 2;
    const lines_raw = malloc(max_lines * 2 * @sizeOf(usize)).?;
    const base_ptr: [*]usize = @ptrCast(@alignCast(lines_raw));
    var count: usize = 0;
    var total_bytes: usize = 0;
    var maxlen: usize = 0;
    {
        var start: usize = 0;
        var i: usize = 0;
        while (i <= data.len) : (i += 1) {
            if (i == data.len or data[i] == '\n') {
                var s = start;
                var e = i;
                if (wpt_mode) {
                    if (e > s and data[e - 1] == '\r') e -= 1;
                } else {
                    while (s < e and isSpace(data[s])) s += 1;
                    while (e > s and isSpace(data[e - 1])) e -= 1;
                }
                if (e > s) {
                    base_ptr[count * 2] = @intFromPtr(data.ptr + s);
                    base_ptr[count * 2 + 1] = e - s;
                    total_bytes += e - s;
                    if (e - s > maxlen) maxlen = e - s;
                    count += 1;
                }
                start = i + 1;
            }
        }
    }
    const lines: []const []const u8 = blk: {
        const p = malloc(count * @sizeOf([]const u8)).?;
        const arr: [*][]const u8 = @ptrCast(@alignCast(p));
        for (0..count) |k| {
            const ptr: [*]const u8 = @ptrFromInt(base_ptr[k * 2]);
            arr[k] = ptr[0..base_ptr[k * 2 + 1]];
        }
        break :blk arr[0..count];
    };

    // NOTE: @min/@max narrow to the comptime bound's int width — force usize
    // or the capacity math overflows in safe builds / truncates in fast ones.
    const out_cap = 6 * maxlen + 96 * @as(usize, @min(maxlen, 16384)) + 2048;
    const scratch_cap = maxlen + 368 * @as(usize, @min(maxlen, 49152)) + 512;
    const out_mem = malloc(out_cap).?;
    const scratch_mem = malloc(scratch_cap).?;
    const out: []u8 = @as([*]u8, @ptrCast(out_mem))[0..out_cap];
    const scratch: []u8 = @as([*]u8, @ptrCast(scratch_mem))[0..scratch_cap];
    var u: url.Url = undefined;

    if (std.mem.eql(u8, mode, "dump")) {
        for (lines) |line| {
            if (url.parse(line, out, scratch, &u)) {
                emit(u.href);
            } else {
                emit("INVALID");
            }
        }
        flushOut();
        return;
    }

    if (wpt_mode) {
        // hex(base)\thex(input) per line -> "href\torigin" | INVALID | BASE_INVALID
        const half = maxlen / 2 + 8;
        const dec_mem = malloc(2 * half).?;
        const dec1: []u8 = @as([*]u8, @ptrCast(dec_mem))[0..half];
        const dec2: []u8 = @as([*]u8, @ptrCast(dec_mem))[half .. 2 * half];
        const linebuf: []u8 = @as([*]u8, @ptrCast(malloc(2 * out_cap + 16).?))[0 .. 2 * out_cap + 16];
        const base_out: []u8 = @as([*]u8, @ptrCast(malloc(out_cap).?))[0..out_cap];
        var bu: url.Url = undefined;
        for (lines) |line| {
            const tab = std.mem.indexOfScalar(u8, line, '\t') orelse line.len;
            const base = hexDecode(line[0..tab], dec1) orelse dec1[0..0];
            const input = if (tab == line.len) dec2[0..0] else (hexDecode(line[tab + 1 ..], dec2) orelse dec2[0..0]);
            if (base.len > 0) {
                if (!url.parse(base, base_out, scratch, &bu)) {
                    emit("BASE_INVALID");
                    continue;
                }
                if (!url.parseBase(input, &bu, out, scratch, &u)) {
                    emit("INVALID");
                    continue;
                }
            } else {
                if (!url.parse(input, out, scratch, &u)) {
                    emit("INVALID");
                    continue;
                }
            }
            const org = u.origin(linebuf[out_cap..], scratch);
            @memcpy(linebuf[0..u.href.len], u.href);
            linebuf[u.href.len] = '\t';
            @memcpy(linebuf[u.href.len + 1 ..][0..org.len], org);
            emit(linebuf[0 .. u.href.len + 1 + org.len]);
        }
        flushOut();
        return;
    }

    if (!std.mem.eql(u8, mode, "bench")) {
        printStr("unknown mode\n");
        return;
    }

    // calibrate rounds to ~1.5s unless given
    var sink: usize = 0;
    {
        const t0 = nowNs();
        for (lines) |line| {
            if (url.parse(line, out, scratch, &u)) sink +%= u.href.len;
        }
        const dt = nowNs() - t0;
        if (rounds == 0) {
            rounds = @intCast(@max(10, @min(1000, 1_500_000_000 / @max(dt, 1))));
        }
    }
    std.mem.doNotOptimizeAway(&sink);

    // warmup
    var invalid: usize = 0;
    for (0..3) |_| {
        invalid = 0;
        for (lines) |line| {
            if (url.parse(line, out, scratch, &u)) {
                sink +%= u.href.len;
            } else invalid += 1;
        }
    }

    var best: u64 = std.math.maxInt(u64);
    for (0..rounds) |_| {
        const t0 = nowNs();
        if (use_alloc) {
            for (lines) |line| {
                const om = malloc(out_cap + scratch_cap).?;
                const o: []u8 = @as([*]u8, @ptrCast(om))[0..out_cap];
                const s: []u8 = @as([*]u8, @ptrCast(om))[out_cap .. out_cap + scratch_cap];
                if (url.parse(line, o, s, &u)) sink +%= u.href.len;
                free(om);
            }
        } else {
            for (lines) |line| {
                if (url.parse(line, out, scratch, &u)) sink +%= u.href.len;
            }
        }
        const dt = nowNs() - t0;
        if (dt < best) best = dt;
    }
    std.mem.doNotOptimizeAway(&sink);

    var mbuf: [256]u8 = undefined;
    const ns_per_url = @as(f64, @floatFromInt(best)) / @as(f64, @floatFromInt(count));
    const gbs = @as(f64, @floatFromInt(total_bytes)) / @as(f64, @floatFromInt(best));
    const msg = std.fmt.bufPrint(&mbuf, "urls={d} bytes={d} invalid={d} best={d}ns -> {d:.2} ns/url, {d:.3} GB/s, {d:.2} Murl/s (rounds={d}, alloc={})\n", .{
        count, total_bytes, invalid, best, ns_per_url, gbs, 1000.0 / ns_per_url, rounds, use_alloc,
    }) catch unreachable;
    printStr(msg);
}
