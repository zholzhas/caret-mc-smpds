const parser = @import("parser.zig");
const processor = @import("processor.zig");
const gbuchi = @import("gbuchi.zig");
const sm_bpds = @import("sm_bpds.zig");
const hr = @import("head_reachability.zig");
const builtin = @import("builtin");
const std = @import("std");

const debug = false;

var naive: bool = false;
var mem_check: bool = false;
var is_json: bool = false;
var substr_ap: bool = false;
var progress: ?std.Progress.Node = null;
var hang = false;

fn parse_args(args: [][:0]u8) void {
    for (args[2..]) |arg| {
        var strip_ind: usize = 0;
        for (arg, 0..) |b, i| {
            if (b != '-') {
                strip_ind = i;
                break;
            }
        }
        const arg_stripped = arg[strip_ind..];
        if (std.mem.eql(u8, arg_stripped, "dpn")) {
            naive = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "mem")) {
            mem_check = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "json")) {
            is_json = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "hang")) {
            hang = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "nohang")) {
            hang = false;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "substr")) {
            substr_ap = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "pytest")) {
            substr_ap = false;
            is_json = true;
            mem_check = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "bin")) {
            substr_ap = true;
            is_json = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "progress")) {
            progress = std.Progress.start(.{});
            continue;
        }
        std.log.err("Unknown argument {s}\n", .{arg_stripped});
    }
}

const RlimitError = error{FailedToSetRlimit};

pub fn main() !void {
    const limit = std.os.linux.rlimit{
        .cur = 12 * 1024 * 1024 * 1024,
        .max = 14 * 1024 * 1024 * 1024,
    };
    const rlimit_res = std.os.linux.setrlimit(.AS, &limit);
    if (rlimit_res != 0) {
        return RlimitError.FailedToSetRlimit;
    }

    var timer = try std.time.Timer.start();
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var gpa = std.heap.GeneralPurposeAllocator(.{}).init;
    _ = &gpa;
    _ = &timer;

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    parse_args(args);

    if (args.len < 2) {
        std.log.err("Provide a filename\n", .{});
        return error.OtherError;
    }

    // const parsed = if (is_json) try reader.parseJsonFromPython(allocator, args[1]) else try parse_smdpn_file(allocator, args[1]);
    // var strat: reader.APStrategy = undefined;
    // if (naive and substr_ap) {
    //     strat = .naive_substr;
    // } else if (naive and !substr_ap) {
    //     strat = .naive;
    // } else if (substr_ap) {
    //     strat = .substr;
    // } else {
    //     strat = .eql;
    // }

    // defer if (progress) |p| p.end();

    // const res = ctl_model_check(gpa.allocator(), parsed, strat, naive, progress) catch |e| {
    //     std.log.err("OOM", .{});

    //     const f_time: f64 = @floatFromInt(timer.lap());
    //     const f_mem: f64 = @floatFromInt(arena.queryCapacity());
    //     std.log.err("Memory used: {d:.3} KB", .{f_mem / 1024});
    //     std.log.err("Time took: {d:.3}s", .{f_time / 1000000000});
    //     return e;
    // };

    // const stdout = std.io.getStdOut().writer();

    // try stdout.print("{s}\n", .{if (res) "True" else "False"});
    // if (mem_check) {
    //     const f_time: f64 = @floatFromInt(timer.lap());
    //     const f_mem: f64 = @floatFromInt(arena.queryCapacity());
    //     try stdout.print("Memory used: {d:.3} KB\n", .{f_mem / 1024});
    //     try stdout.print("Time took: {d:.3}s\n", .{f_time / 1000000000});
    // }

    // if (hang) {
    //     const stdin = std.io.getStdIn().reader();

    //     try stdout.print("{{END}}\n", .{});
    //     _ = try stdin.readByte();
    // }
}

pub fn parse_smdpn_file(allocator: std.mem.Allocator, filename: []const u8) !parser.ParsedSMPDS {
    var file = parser.SmpdsFile.open(allocator, filename);
    const unprocessed_conf = try file.parse();
    return unprocessed_conf;
}

pub fn caret_model_check(
    gpa: std.mem.Allocator,
    arena: std.mem.Allocator,
    proc: *processor.SM_PDS_Processor,
    conf: processor.Conf,
    formula: processor.Caret.Formula,
) !bool {
    var gbpds = gbuchi.SM_GBPDS_Processor.init(gpa, arena);
    defer gbpds.deinit();

    const closure = try formula.get_closure(gpa);
    defer {
        for (closure) |f| {
            f.deinit(gpa);
        }
        gpa.free(closure);
    }

    const atoms = try gbuchi.Atom.getAtoms(gpa, closure);
    defer {
        for (atoms) |*a| {
            a.deinit();
        }
        gpa.free(atoms);
    }

    var lambda = try processor.LabellingFunction.init(gpa, proc, formula);
    defer lambda.deinit();

    try gbpds.construct(proc, atoms, lambda);

    var ginits = std.ArrayList(gbuchi.StateName).init(gpa);
    defer ginits.deinit();

    for (atoms) |*atom| {
        if (!atom.set.contains(formula)) continue;
        if (!atom.calFormsEmpty()) continue;

        try ginits.append(try gbpds.getStateName(gbuchi.State{
            .control_point = conf.state,
            .atom = atom,
            .label = .unexit,
        }));
    }

    try gbpds.simplify(ginits.items);

    var smb = sm_bpds.SM_BPDS_Processor.init(gpa, arena, &gbpds);
    defer smb.deinit();

    try smb.construct();

    var binits = std.ArrayList(sm_bpds.StateName).init(gpa);
    defer binits.deinit();

    for (atoms) |*atom| {
        if (!atom.set.contains(formula)) continue;
        if (!atom.calFormsEmpty()) continue;

        try binits.append(try smb.getStateName(sm_bpds.State{
            .general = gbuchi.State{
                .control_point = conf.state,
                .atom = atom,
                .label = .unexit,
            },
            .counter = 0,
        }));
    }

    try smb.simplify(binits.items);

    var ma = sm_bpds.MA.init(arena, gpa);
    defer ma.deinit();

    try ma.saturate(&smb, false);

    var hrg = hr.HeadReachabilityGraph.init(arena, gpa, &ma, &smb);
    defer hrg.deinit();

    try hrg.construct();

    const sccs = try hrg.findRepeatingHeads(gpa);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }

    var hr_ma = sm_bpds.MA.init(arena, gpa);
    defer hr_ma.deinit();

    try hr.build_hr_pre(&hr_ma, sccs);

    try hr_ma.saturate(&smb, true);

    const smb_init_word = try arena.alloc(sm_bpds.SymbolName, conf.stack.len);

    for (0..conf.stack.len) |i| {
        smb_init_word[i] = try gbpds.getSymbolName(.{ .standard = conf.stack[i] });
    }

    var res = false;
    for (atoms) |*atom| {
        if (!atom.set.contains(formula)) continue;
        if (!atom.calFormsEmpty()) continue;
        res = res or try hr_ma.accepts(.{ .st = .{
            .state = try smb.getStateName(.{ .counter = 0, .general = .{
                .control_point = conf.state,
                .atom = atom,
                .label = .unexit,
            } }),
            .phase = conf.phase,
        } }, smb_init_word);
    }
    return res;
}

pub fn caret_model_check_file(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    var proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(arena, filename);

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const conf = try proc.getInit(unprocessed_conf.init);

    const formula = try processor.processCaret(arena, unprocessed_conf.caret);

    return caret_model_check(gpa, arena, &proc, conf, formula);
}

test "whole" {
    if (debug) {
        try std.testing.expect(true);
        return;
    }
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const cwd = std.fs.cwd();
    const test_dir = try cwd.openDir("tests", .{
        .iterate = true,
    });

    var test_file_iter = test_dir.iterate();
    while (try test_file_iter.next()) |file| {
        if (file.kind == .file and std.mem.endsWith(u8, file.name, ".smpds")) {
            // std.debug.print("testing {s}\n", .{file.name});
            const name = file.name;

            const res = try caret_model_check_file(gpa, arena.allocator(), try test_dir.realpathAlloc(arena.allocator(), file.name));

            std.testing.expectEqual(std.mem.startsWith(u8, name, "true"), res) catch |err| {
                std.debug.print("Failed {s}\n", .{name});
                return err;
            };
        }
    }
}

// test "naive" {
//     const gpa = std.testing.allocator;
//     var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
//     defer arena.deinit();
//     const allocator = arena.allocator();

//     const cwd = std.fs.cwd();
//     const test_dir = try cwd.openDir("tests", .{
//         .iterate = true,
//     });

//     var test_file_iter = test_dir.iterate();
//     while (try test_file_iter.next()) |file| {
//         if (file.kind == .file and std.mem.endsWith(u8, file.name, ".smdpn")) {
//             // std.debug.print("testing {s}\n", .{file.name});
//             const name = file.name;

//             const parsed = try parse_smdpn_file(allocator, try test_dir.realpathAlloc(allocator, file.name));
//             const res = try ctl_model_check(gpa, parsed, .naive, true, null);

//             std.testing.expectEqual(std.mem.startsWith(u8, name, "true"), res) catch |err| {
//                 std.debug.print("Failed {s}\n", .{name});
//                 return err;
//             };
//         }
//     }
// }

test "dependencies" {
    _ = parser.SM_PDS;
    _ = processor.SM_PDS_Processor;
    _ = gbuchi.Atom;
    _ = hr.HeadReachabilityGraph;
}

test "full" {
    if (!debug) {
        try std.testing.expect(true);
        return;
    }
    var timer = try std.time.Timer.start();
    const gpa = std.testing.allocator;

    var arena_ = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_.deinit();
    const arena = arena_.allocator();

    var proc = processor.SM_PDS_Processor.init(arena, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(arena, "examples/full_test.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const conf = try proc.getInit(unprocessed_conf.init);

    var gbpds = gbuchi.SM_GBPDS_Processor.init(gpa, arena);
    defer gbpds.deinit();

    const formula = try processor.processCaret(arena, unprocessed_conf.caret);

    const closure = try formula.get_closure(gpa);
    defer {
        for (closure) |f| {
            f.deinit(gpa);
        }
        gpa.free(closure);
    }

    const atoms = try gbuchi.Atom.getAtoms(gpa, closure);
    defer {
        for (atoms) |*a| {
            a.deinit();
        }
        gpa.free(atoms);
    }

    var lambda = try processor.LabellingFunction.init(gpa, &proc, formula);
    defer lambda.deinit();

    try gbpds.construct(&proc, atoms, lambda);

    var ginits = std.ArrayList(gbuchi.StateName).init(gpa);
    defer ginits.deinit();

    for (atoms) |*atom| {
        if (!atom.set.contains(formula)) continue;
        if (!atom.calFormsEmpty()) continue;

        try ginits.append(try gbpds.getStateName(gbuchi.State{
            .control_point = conf.state,
            .atom = atom,
            .label = .unexit,
        }));
    }

    try gbpds.simplify(ginits.items);

    var gen_printer = try gbuchi.SM_GBPDS_Printer.init(gpa, &proc);
    defer gen_printer.deinit();
    for (gbpds.rule_set.keys()) |r| {
        std.debug.print("{}\n", .{gen_printer.rule(r)});
    }

    var smb = sm_bpds.SM_BPDS_Processor.init(gpa, arena, &gbpds);
    defer smb.deinit();

    try smb.construct();

    var binits = std.ArrayList(sm_bpds.StateName).init(gpa);
    defer binits.deinit();

    for (atoms) |*atom| {
        if (!atom.set.contains(formula)) continue;
        if (!atom.calFormsEmpty()) continue;

        try binits.append(try smb.getStateName(sm_bpds.State{
            .general = gbuchi.State{
                .control_point = conf.state,
                .atom = atom,
                .label = .unexit,
            },
            .counter = 0,
        }));
    }

    try smb.simplify(binits.items);

    var b_printer = sm_bpds.SM_BPDS_Printer.init(&gen_printer);
    for (smb.rules.keys()) |rule| {
        std.debug.print("{}\n", .{b_printer.rule(rule)});
    }

    var ma_printer = sm_bpds.MA.Printer.init(&b_printer);

    var ma = sm_bpds.MA.init(arena, gpa);
    defer ma.deinit();

    try ma.saturate(&smb, false);

    {
        var edge_it = ma.edge_set.keyIterator();
        while (edge_it.next()) |edge| {
            std.debug.print("{}\n", .{ma_printer.edge(edge.*)});
        }
    }

    var hrg = hr.HeadReachabilityGraph.init(arena, gpa, &ma, &smb);
    defer hrg.deinit();

    var hr_printer = hr.HeadReachabilityGraph.Printer.init(&b_printer);

    hr.HeadReachabilityGraph.global_printer = &hr_printer;
    defer hr.HeadReachabilityGraph.global_printer = null;

    try hrg.construct();

    {
        for (hrg.edges.keys()) |edge| {
            std.debug.print("{}\n", .{hr_printer.edge(edge)});
        }
    }

    const sccs = try hrg.findRepeatingHeads(gpa);
    defer {
        for (sccs) |scc| {
            gpa.free(scc.heads);
        }
        gpa.free(sccs);
    }
    for (sccs) |scc| {
        for (scc.heads) |h| {
            std.debug.print("{} {}\n", .{ b_printer.state(h.state.*), gen_printer.symbol(h.top.*) });
        }
    }

    var hr_ma = sm_bpds.MA.init(arena, gpa);
    defer hr_ma.deinit();

    try hr.build_hr_pre(&hr_ma, sccs);

    try hr_ma.saturate(&smb, true);

    {
        var edge_it = hr_ma.edge_set.keyIterator();
        while (edge_it.next()) |edge| {
            std.debug.print("{}\n", .{ma_printer.edge(edge.*)});
        }
    }

    const smb_init_word = try arena.alloc(sm_bpds.SymbolName, conf.stack.len);

    for (0..conf.stack.len) |i| {
        smb_init_word[i] = try gbpds.getSymbolName(.{ .standard = conf.stack[i] });
    }

    var res = false;
    for (atoms) |*atom| {
        if (!atom.set.contains(formula)) continue;
        if (!atom.calFormsEmpty()) continue;
        res = res or try hr_ma.accepts(.{ .st = .{
            .state = try smb.getStateName(.{ .counter = 0, .general = .{
                .control_point = conf.state,
                .atom = atom,
                .label = .unexit,
            } }),
            .phase = conf.phase,
        } }, smb_init_word);
    }

    std.debug.print("{s}\n", .{if (res) "True" else "False"});

    std.debug.print("{d:.3}s\n", .{@as(f64, @floatFromInt(sm_bpds.MA.add_edge_time)) / 1000000000});
    std.debug.print("{d:.3}s\n", .{@as(f64, @floatFromInt(sm_bpds.MA.path_time)) / 1000000000});
    std.debug.print("{d:.3}s\n", .{@as(f64, @floatFromInt(sm_bpds.MA.sm_time)) / 1000000000});
    std.debug.print("Total: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});
}
