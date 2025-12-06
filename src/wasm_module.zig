const parser = @import("parser.zig");
const processor = @import("processor.zig");
const gbuchi = @import("gbuchi.zig");
const sm_bpds = @import("sm_bpds.zig");
const hr = @import("head_reachability.zig");
const builtin = @import("builtin");
const std = @import("std");
const root = @import("main.zig");

extern fn printStr(msg: [*]const u8, len: usize) void;
extern fn printInt(a: i32) void;

const mecha = @import("mecha");

pub export fn alloc(len: usize) ?[*]const u8 {
    const sl = std.heap.wasm_allocator.alloc(u8, len) catch return null;
    return sl.ptr;
}

pub export fn free(ptr: [*]const u8, len: usize) void {
    std.heap.wasm_allocator.free(ptr[0..len]);
}

fn print(str: []const u8) void {
    printStr(str.ptr, str.len);
}

pub export fn read_smpds(smdpn_conf: [*]const u8, len: usize) i32 {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const res = parser.parseString(arena.allocator(), smdpn_conf[0..len]);
    switch (res) {
        .ok => |conf| {
            print("Model Parsed!");
            const mc_res = root.caret_model_check_unproc(std.heap.wasm_allocator, arena.allocator(), conf, processor.LabellingFunction.substr) catch {
                print("Error while model checking!");
                return -1;
            };
            if (mc_res) {
                return 1;
            } else {
                return 0;
            }
        },
        .err => |_| {
            print("Error!");
        },
        .invalid_syntax => |err| {
            print(std.fmt.allocPrint(std.heap.wasm_allocator, "Invalid syntax! Column {}, line {}", .{ err.col, err.line }) catch {
                print("Error printing error!");
                return -1;
            });
        },
    }
    return -1;
}
