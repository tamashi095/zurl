const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{ .preferred_optimize_mode = .ReleaseFast });

    const mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    mod.link_libc = true;
    const exe = b.addExecutable(.{ .name = "zurl", .root_module = mod });
    b.installArtifact(exe);

    const test_mod = b.createModule(.{
        .root_source_file = b.path("src/idna_test.zig"),
        .target = target,
        .optimize = optimize,
    });
    test_mod.link_libc = true;
    const test_exe = b.addExecutable(.{ .name = "zidnatest", .root_module = test_mod });
    b.installArtifact(test_exe);
}
