const parser = @import("parser.zig");
const processor = @import("processor.zig");
const gbuchi = @import("gbuchi.zig");
const sm_bpds = @import("sm_bpds.zig");
const hr = @import("head_reachability.zig");
const builtin = @import("builtin");
const std = @import("std");

const debug = false;

var pytest: bool = false;
var naive: bool = false;

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
        if (std.mem.eql(u8, arg_stripped, "pytest")) {
            pytest = true;
            continue;
        }
        if (std.mem.eql(u8, arg_stripped, "naive")) {
            naive = true;
            continue;
        }
        std.log.err("Unknown argument {s}\n", .{arg_stripped});
    }
}

const RlimitError = error{FailedToSetRlimit};

pub const GlobalState = struct {
    timer: *std.time.Timer,
    errors: []const u8,

    arena: *std.heap.ArenaAllocator,
};

pub var state: GlobalState = undefined;

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

    state = GlobalState{
        .timer = &timer,
        .arena = &arena,
        .errors = &.{},
    };

    var gpa = std.heap.GeneralPurposeAllocator(.{}).init;
    _ = &gpa;
    _ = &timer;

    const args = try std.process.argsAlloc(arena.allocator());
    defer std.process.argsFree(arena.allocator(), args);

    parse_args(args);

    if (args.len < 2) {
        std.log.err("Provide a filename\n", .{});
        return error.OtherError;
    }

    var result: bool = undefined;
    if (pytest) {
        if (naive) {
            result = caret_model_check_pytest_naive(gpa.allocator(), arena.allocator(), args[1]) catch |e| blk: {
                print_errors(e);
                break :blk false;
            };
        } else {
            result = caret_model_check_pytest(gpa.allocator(), arena.allocator(), args[1]) catch |e| blk: {
                print_errors(e);
                break :blk false;
            };
        }
    } else {
        result = caret_model_check_smpds_file(gpa.allocator(), arena.allocator(), args[1]) catch |e| blk: {
            print_errors(e);
            break :blk false;
        };
    }

    const stdout = std.io.getStdOut().writer();

    try stdout.print("{s}\n", .{if (result) "True" else "False"});

    if (pytest) {
        const f_time: f64 = @floatFromInt(timer.lap());
        const f_mem: f64 = @floatFromInt(arena.queryCapacity());
        try stdout.print("Memory used: {d:.3} KB\n", .{f_mem / 1024});
        try stdout.print("Time took: {d:.3}s\n", .{f_time / 1000000000});
    }
}

pub fn print_errors(_: anyerror) void {
    std.log.err("OOM", .{});

    const f_time: f64 = @floatFromInt(state.timer.lap());
    const f_mem: f64 = @floatFromInt(state.arena.queryCapacity());
    std.log.err("Memory used: {d:.3} KB", .{f_mem / 1024});
    std.log.err("Time took: {d:.3}s", .{f_time / 1000000000});
}

pub fn parse_smpds_file(allocator: std.mem.Allocator, filename: []const u8) !parser.ParsedSMPDS {
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
    lambda: processor.LabellingFunction,
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

pub fn caret_model_check_unproc(gpa: std.mem.Allocator, arena: std.mem.Allocator, unprocessed_conf: parser.ParsedSMPDS, lfunc: processor.LabellingFunction.Labeller) !bool {
    var proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    const conf = try proc.getInit(unprocessed_conf.init);

    const formula = try processor.processCaret(arena, unprocessed_conf.caret);

    var lambda = try processor.LabellingFunction.init(gpa, &proc, formula, lfunc);
    defer lambda.deinit();

    return caret_model_check(gpa, arena, &proc, conf, formula, lambda);
}

pub fn caret_model_check_smpds_file(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    var file = parser.SmpdsFile.open(arena, filename);
    const unprocessed_conf = try file.parse();

    return caret_model_check_unproc(gpa, arena, unprocessed_conf, processor.LabellingFunction.strict);
}

pub fn caret_model_check_pytest(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    const unprocessed_conf = try parser.parseJsonFromPython(arena, filename);

    return caret_model_check_unproc(gpa, arena, unprocessed_conf, processor.LabellingFunction.strict);
}

pub fn caret_model_check_smpds_naive(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    var file = parser.SmpdsFile.open(arena, filename);
    const unprocessed_conf = try file.parse();
    var proc = processor.SM_PDS_Processor.init(arena, gpa);

    defer proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    _ = try proc.getInit(unprocessed_conf.init);

    const pds = try translate_to_naive(gpa, arena, &proc, unprocessed_conf);
    var pds_proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer pds_proc.deinit();

    try pds_proc.process(pds.smpds, pds.init);
    const pds_conf = try pds_proc.getInit(pds.init);

    const formula = try processor.processCaret(arena, pds.caret);

    var lambda = try processor.LabellingFunction.init(gpa, &pds_proc, formula, processor.LabellingFunction.naive);
    defer lambda.deinit();

    return caret_model_check(gpa, arena, &pds_proc, pds_conf, formula, lambda);
}

pub fn caret_model_check_pytest_naive(gpa: std.mem.Allocator, arena: std.mem.Allocator, filename: []const u8) !bool {
    const unprocessed_conf = try parser.parseJsonFromPython(arena, filename);
    var proc = processor.SM_PDS_Processor.init(arena, gpa);

    defer proc.deinit();

    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    _ = try proc.getInit(unprocessed_conf.init);

    const pds = try translate_to_naive(gpa, arena, &proc, unprocessed_conf);
    var pds_proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer pds_proc.deinit();

    try pds_proc.process(pds.smpds, pds.init);
    const pds_conf = try pds_proc.getInit(pds.init);

    const formula = try processor.processCaret(arena, pds.caret);

    var lambda = try processor.LabellingFunction.init(gpa, &pds_proc, formula, processor.LabellingFunction.naive);
    defer lambda.deinit();

    return caret_model_check(gpa, arena, &pds_proc, pds_conf, formula, lambda);
}

pub fn translate_to_naive(
    gpa: std.mem.Allocator,
    arena: std.mem.Allocator,
    proc: *processor.SM_PDS_Processor,
    unprocessed_conf: parser.ParsedSMPDS,
) !parser.ParsedSMPDS {
    var rules = std.ArrayList(parser.Rule).init(gpa);
    defer rules.deinit();

    const init_phase_name = try proc.process_phase(unprocessed_conf.init.phase);

    var res_init_phase = std.ArrayList([]const u8).init(gpa);
    defer res_init_phase.deinit();

    for (proc.phases.keys()) |phase_name| {
        const phase = proc.phase_names.phase_values.get(phase_name).?;
        rule_loop: for (unprocessed_conf.smpds.rules) |rule| {
            const r_name = proc.rule_names.rule_map.get(rule.name).?;
            if (phase.items.contains(r_name)) {
                switch (rule.typ) {
                    .sm => {
                        const old_phase = try proc.process_phase(rule.sm_l.?);
                        const new_phase = try proc.process_phase(rule.sm_r.?);
                        const res_phase = proc.phase_combiner.get(.{
                            .original_phase = phase_name,
                            .to_add = new_phase,
                            .to_remove = old_phase,
                        }) orelse continue :rule_loop;

                        for (unprocessed_conf.smpds.alphabet) |top| {
                            const lab = try std.fmt.allocPrint(arena, "{}", .{rules.items.len});
                            const new_rule = parser.Rule{
                                .from = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.from, phase_name }),
                                .to = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.to, res_phase }),
                                .name = lab,
                                .top = top,
                                .new_top = top,
                                .typ = .internal,
                            };
                            try rules.append(new_rule);
                            try res_init_phase.append(lab);
                        }
                    },
                    .call, .internal, .ret => {
                        const lab = try std.fmt.allocPrint(arena, "{}", .{rules.items.len});
                        const new_rule = parser.Rule{
                            .from = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.from, phase_name }),
                            .to = try std.fmt.allocPrint(arena, "{s}#{}", .{ rule.to, phase_name }),
                            .name = lab,
                            .top = rule.top.?,
                            .new_top = rule.new_top,
                            .new_tail = rule.new_tail,
                            .typ = rule.typ,
                        };
                        try rules.append(new_rule);
                        try res_init_phase.append(lab);
                    },
                }
            }
        }
    }

    const init_conf = parser.Conf{
        .state = try std.fmt.allocPrint(arena, "{s}#{}", .{ unprocessed_conf.init.state, init_phase_name }),
        .phase = try arena.dupe([]const u8, res_init_phase.items),
        .stack = unprocessed_conf.init.stack,
    };

    var states = std.StringArrayHashMap(void).init(gpa);
    defer states.deinit();
    var alphabet = std.StringArrayHashMap(void).init(gpa);
    defer alphabet.deinit();

    for (rules.items) |rule| {
        try states.put(rule.from, {});
        try states.put(rule.to, {});
        if (rule.top) |sym| {
            try alphabet.put(sym, {});
        }
        if (rule.new_top) |sym| {
            try alphabet.put(sym, {});
        }
        if (rule.new_tail) |sym| {
            try alphabet.put(sym, {});
        }
    }
    const states_sorted = try arena.dupe([]const u8, states.keys());
    std.mem.sort([]const u8, states_sorted, {}, parser.lt);
    const alphabet_sorted = try arena.dupe([]const u8, alphabet.keys());
    std.mem.sort([]const u8, alphabet_sorted, {}, parser.lt);

    const smpds = parser.SM_PDS{
        .states = states_sorted,
        .alphabet = alphabet_sorted,
        .rules = try arena.dupe(parser.Rule, rules.items),
    };

    return parser.ParsedSMPDS{
        .smpds = smpds,
        .init = init_conf,
        .caret = unprocessed_conf.caret,
    };
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

            const res = try caret_model_check_smpds_file(gpa, arena.allocator(), try test_dir.realpathAlloc(arena.allocator(), file.name));

            std.testing.expectEqual(std.mem.startsWith(u8, name, "true"), res) catch |err| {
                std.debug.print("Failed {s}\n", .{name});
                return err;
            };
        }
    }
}

test "naive" {
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

            const res = try caret_model_check_smpds_naive(gpa, arena.allocator(), try test_dir.realpathAlloc(arena.allocator(), file.name));

            std.testing.expectEqual(std.mem.startsWith(u8, name, "true"), res) catch |err| {
                std.debug.print("Failed naive {s}\n", .{name});
                return err;
            };
        }
    }
}

test "dependencies" {
    _ = parser.SM_PDS;
    _ = processor.SM_PDS_Processor;
    _ = gbuchi.Atom;
    _ = hr.HeadReachabilityGraph;
}

test "debug" {
    if (!debug) {
        try std.testing.expect(true);
        return;
    }
    var timer = try std.time.Timer.start();
    const gpa = std.testing.allocator;

    var arena_ = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_.deinit();
    const arena = arena_.allocator();

    var proc_ = processor.SM_PDS_Processor.init(arena, std.testing.allocator);
    defer proc_.deinit();

    var file = parser.SmpdsFile.open(arena, "tests/true-2.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc_.process(unprocessed, unprocessed_conf.init);
    _ = try proc_.getInit(unprocessed_conf.init);

    const pds = try translate_to_naive(gpa, arena, &proc_, unprocessed_conf);

    for (pds.smpds.rules) |r| {
        std.debug.print("{}\n", .{r});
    }
    std.debug.print("{}\n", .{pds.init});

    var proc = processor.SM_PDS_Processor.init(arena, gpa);
    defer proc.deinit();

    try proc.process(pds.smpds, pds.init);
    const conf = try proc.getInit(pds.init);

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

    var lambda = try processor.LabellingFunction.init(gpa, &proc, formula, processor.LabellingFunction.naive);
    defer lambda.deinit();

    // const aps = lambda.getAPs(conf.state);
    // for (aps.keys()) |ap| {
    //     std.debug.print("AP: {s}\n", .{ap});
    // }
    // for (atoms) |a| {
    //     std.debug.print("{}\n", .{a});
    //     std.debug.print("{}\n", .{a.containsAPsExactly(lambda.getAPs(conf.state))});
    // }

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

    // try gbpds.simplify(ginits.items);

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
