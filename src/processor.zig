const Unprocessed = @import("parser.zig");
const std = @import("std");
const parser = @import("parser.zig");

pub const State = u32;
pub const Symbol = u32;
pub const RuleName = u32;
pub const PhaseName = u32;
pub const Conf = struct {
    state: State,
    stack: []Symbol,
    phase: PhaseName,
};

pub const InternalRule = struct { from: State, top: Symbol, to: State, new_top: ?Symbol, new_tail: ?Symbol };

pub const CallRule = struct { from: State, top: Symbol, to: State, new_top: Symbol, new_tail: Symbol };

pub const RetRule = struct { from: State, top: Symbol, to: State };

pub const SMRule = struct { from: State, old_phase: PhaseName, new_phase: PhaseName, to: State };

pub const Rule = union(enum) {
    int: InternalRule,
    call: CallRule,
    ret: RetRule,
    sm: SMRule,
};

pub const LabelledRule = struct {
    label: RuleName,
    rule: Rule,
};

pub fn Pair(comptime F: type, comptime S: type) type {
    return struct {
        first: F,
        second: S,
    };
}

pub const SM_PDS = struct {
    states: []const State,
    alphabet: []const Symbol,
    rules: std.ArrayList(LabelledRule),
    end_of_stack: Symbol,

    init_conf: Conf,

    phases: *PhaseProcessor,
};

pub fn Set(comptime T: type) type {
    return struct { items: std.AutoArrayHashMap(T, void) };
}

pub fn SetContext(comptime T: type) type {
    return struct {
        pub fn hash(_: @This(), v: Set(T)) u32 {
            var sum: u32 = 0;
            for (v.items.keys()) |item| {
                sum ^= std.hash.Murmur3_32.hashUint32(item);
            }
            return sum;
        }

        pub fn eql(_: @This(), left: Set(T), right: Set(T), _: usize) bool {
            return left.items.count() == right.items.count() and blk: {
                for (left.items.keys()) |item| {
                    if (!right.items.contains(item)) {
                        break :blk false;
                    }
                }
                break :blk true;
            };
        }
    };
}

const RuleNameProcessor = struct {
    rule_map: std.StringArrayHashMap(RuleName),
    var rule_name_offset: RuleName = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{ .rule_map = std.StringArrayHashMap(RuleName).init(allocator) };
    }

    pub fn get_rule_name(self: *@This(), label: []const u8) !RuleName {
        return self.rule_map.get(label) orelse blk: {
            const name = rule_name_offset;
            rule_name_offset += 1;
            try self.rule_map.put(label, name);
            break :blk name;
        };
    }
};

pub const PhaseProcessor = struct {
    phase_map: std.ArrayHashMap(Set(RuleName), PhaseName, SetContext(RuleName), true),
    phase_values: std.AutoArrayHashMap(PhaseName, Set(RuleName)),

    var phase_name_offset: PhaseName = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{
            .phase_map = std.ArrayHashMap(Set(RuleName), PhaseName, SetContext(RuleName), true).init(allocator),
            .phase_values = std.AutoArrayHashMap(PhaseName, Set(RuleName)).init(allocator),
        };
    }

    pub fn get_phase_name(self: *@This(), label: Set(RuleName)) !PhaseName {
        return self.phase_map.get(label) orelse blk: {
            const name = phase_name_offset;
            phase_name_offset += 1;
            try self.phase_map.put(label, name);
            try self.phase_values.put(name, label);
            break :blk name;
        };
    }
};

pub const StateProcessor = struct {
    state_map: std.StringArrayHashMap(State),
    var state_name_offset: State = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{ .state_map = std.StringArrayHashMap(State).init(allocator) };
    }

    pub fn get_state_name(self: *@This(), label: []const u8) !State {
        return self.state_map.get(label) orelse blk: {
            const name = state_name_offset;
            state_name_offset += 1;
            try self.state_map.put(label, name);
            break :blk name;
        };
    }
};

pub const SymbolProcessor = struct {
    symbol_map: std.StringArrayHashMap(Symbol),
    symbol_names: std.AutoArrayHashMap(Symbol, []const u8),
    var symbol_name_offset: Symbol = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{
            .symbol_map = std.StringArrayHashMap(Symbol).init(allocator),
            .symbol_names = std.AutoArrayHashMap(Symbol, []const u8).init(allocator),
        };
    }

    pub fn get_symbol_name(self: *@This(), label: []const u8) !Symbol {
        return self.symbol_map.get(label) orelse blk: {
            const name = symbol_name_offset;
            symbol_name_offset += 1;
            try self.symbol_map.put(label, name);
            try self.symbol_names.put(name, label);
            break :blk name;
        };
    }
};

pub const LabellingFunction = struct {
    pub const Key = struct {
        state: State,
        top: Symbol,
    };

    state_aps: std.AutoArrayHashMap(Key, std.StringArrayHashMap(void)),

    pub const Labeller = *const fn ([]const u8, []const u8) bool;

    pub fn init(gpa: std.mem.Allocator, proc: *SM_PDS_Processor, formula: Caret.Formula, func: Labeller, valuations: []const parser.Valuation, init_conf: *Conf) !LabellingFunction {
        var state_names = std.AutoHashMap(State, []const u8).init(gpa);
        defer state_names.deinit();
        var state_aps = std.AutoArrayHashMap(Key, std.StringArrayHashMap(void)).init(gpa);

        for (proc.states.state_map.keys()) |name| {
            try state_names.put(proc.states.state_map.get(name).?, name);
            for (proc.symbols.symbol_map.keys()) |symbol| {
                try state_aps.put(.{ .state = proc.states.state_map.get(name).?, .top = proc.symbols.symbol_map.get(symbol).? }, std.StringArrayHashMap(void).init(gpa));
            }
        }

        const alphabet = proc.symbols.symbol_map.keys();

        var dfas = std.ArrayList(DFA).init(gpa);
        defer {
            for (dfas.items) |*dfa| {
                dfa.deinit();
            }
            dfas.deinit();
        }

        var unique_dfas = std.StringHashMap(usize).init(gpa);
        defer {
            var keyit = unique_dfas.keyIterator();
            while (keyit.next()) |k| {
                gpa.free(k.*);
            }
            unique_dfas.deinit();
        }

        var ap_dfas = std.StringHashMap(std.AutoHashMap(State, usize)).init(gpa);
        defer {
            var it = ap_dfas.iterator();
            while (it.next()) |k| {
                k.value_ptr.deinit();
            }
            ap_dfas.deinit();
        }

        for (valuations) |val| {
            const gop = try ap_dfas.getOrPut(val.ap);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoHashMap(State, usize).init(gpa);
            }
            switch (val.val) {
                .regular => |reg| {
                    const regstr = try std.fmt.allocPrint(gpa, "{}", .{reg.regex.*});
                    defer gpa.free(regstr);

                    const dfa_gop = try unique_dfas.getOrPut(regstr);
                    if (!dfa_gop.found_existing) {
                        dfa_gop.key_ptr.* = try gpa.dupe(u8, regstr);
                        dfa_gop.value_ptr.* = dfas.items.len;
                        var new_nfa = try NFA.initFromRegex(gpa, reg.regex);
                        defer new_nfa.deinit();
                        try new_nfa.regToNfa();
                        new_nfa.reverse();
                        const dfa = try new_nfa.determinize(gpa, alphabet);
                        try dfas.append(dfa);
                        // for (dfa.edges.items) |edge| {
                        //     std.debug.print("{} - {s} -> {}\n", .{ edge.from, edge.sym, edge.to });
                        // }
                        // std.debug.print("Start: {}\nFinish: {any}\n", .{ dfa.start, dfa.finish.items });
                    }
                    if (reg.state == null) {
                        for (proc.states.state_map.keys()) |st| {
                            try gop.value_ptr.*.put(proc.states.state_map.get(st).?, dfa_gop.value_ptr.*);
                        }
                    } else {
                        try gop.value_ptr.*.put(proc.states.state_map.get(reg.state.?).?, dfa_gop.value_ptr.*);
                    }
                },
                else => {},
            }
        }

        const dfa_set = DFASet{
            .dfas = dfas.items,
        };

        const all_states = try dfa_set.getAllStates(gpa);
        defer {
            for (all_states) |s| {
                gpa.free(s);
            }
            gpa.free(all_states);
        }

        var new_rules = std.ArrayList(LabelledRule).init(gpa);
        defer new_rules.deinit();

        const RegSymbolPair = struct {
            sym: Symbol,
            state: []const DFA.Node,
        };

        var regular_symbols_map = std.AutoArrayHashMap(Symbol, RegSymbolPair).init(gpa);

        defer {
            for (regular_symbols_map.values()) |p| {
                gpa.free(p.state);
            }
            regular_symbols_map.deinit();
        }

        for (proc.system.?.rules.items) |lr| {
            switch (lr.rule) {
                .int => |r| {
                    const topstr = proc.symbols.symbol_names.get(r.top).?;

                    for (all_states) |state| {
                        const topstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ topstr, state });
                        const top2 = try proc.process_symbol(topstr2);
                        if (!regular_symbols_map.contains(top2)) {
                            try regular_symbols_map.put(top2, .{ .sym = r.top, .state = try gpa.dupe(DFA.Node, state) });
                        }
                        if (r.new_top == null) {
                            try new_rules.append(LabelledRule{
                                .label = lr.label,
                                .rule = Rule{
                                    .int = InternalRule{
                                        .from = r.from,
                                        .top = top2,
                                        .to = r.to,
                                        .new_top = null,
                                        .new_tail = null,
                                    },
                                },
                            });
                        } else if (r.new_tail == null) {
                            const new_topstr = proc.symbols.symbol_names.get(r.new_top.?).?;
                            const new_topstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ new_topstr, state });
                            const new_top2 = try proc.process_symbol(new_topstr2);
                            if (!regular_symbols_map.contains(new_top2)) {
                                try regular_symbols_map.put(new_top2, .{ .sym = r.new_top.?, .state = try gpa.dupe(DFA.Node, state) });
                            }
                            try new_rules.append(LabelledRule{
                                .label = lr.label,
                                .rule = Rule{
                                    .int = InternalRule{
                                        .from = r.from,
                                        .top = top2,
                                        .to = r.to,
                                        .new_top = new_top2,
                                        .new_tail = null,
                                    },
                                },
                            });
                        } else {
                            const new_tailstr = proc.symbols.symbol_names.get(r.new_tail.?).?;
                            const new_tailstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ new_tailstr, state });
                            const new_tail2 = try proc.process_symbol(new_tailstr2);
                            if (!regular_symbols_map.contains(new_tail2)) {
                                try regular_symbols_map.put(new_tail2, .{ .sym = r.new_tail.?, .state = try gpa.dupe(DFA.Node, state) });
                            }

                            const newstate = try dfa_set.getEdge(gpa, state, new_tailstr);
                            defer gpa.free(newstate);

                            const new_topstr = proc.symbols.symbol_names.get(r.new_top.?).?;
                            const new_topstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ new_topstr, newstate });
                            const new_top2 = try proc.process_symbol(new_topstr2);
                            if (!regular_symbols_map.contains(new_top2)) {
                                try regular_symbols_map.put(new_top2, .{ .sym = r.new_top.?, .state = try gpa.dupe(DFA.Node, newstate) });
                            }

                            try new_rules.append(LabelledRule{
                                .label = lr.label,
                                .rule = Rule{
                                    .int = InternalRule{
                                        .from = r.from,
                                        .top = top2,
                                        .to = r.to,
                                        .new_top = new_top2,
                                        .new_tail = new_tail2,
                                    },
                                },
                            });
                        }
                    }
                },
                .call => |r| {
                    const topstr = proc.symbols.symbol_names.get(r.top).?;

                    for (all_states) |state| {
                        const topstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ topstr, state });
                        const top2 = try proc.process_symbol(topstr2);

                        if (!regular_symbols_map.contains(top2)) {
                            try regular_symbols_map.put(top2, .{ .sym = r.top, .state = try gpa.dupe(DFA.Node, state) });
                        }

                        const new_tailstr = proc.symbols.symbol_names.get(r.new_tail).?;
                        const new_tailstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ new_tailstr, state });
                        const new_tail2 = try proc.process_symbol(new_tailstr2);

                        const newstate = try dfa_set.getEdge(gpa, state, new_tailstr);
                        defer gpa.free(newstate);

                        const new_topstr = proc.symbols.symbol_names.get(r.new_top).?;
                        const new_topstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ new_topstr, newstate });
                        const new_top2 = try proc.process_symbol(new_topstr2);

                        if (!regular_symbols_map.contains(new_tail2)) {
                            try regular_symbols_map.put(new_tail2, .{ .sym = r.new_tail, .state = try gpa.dupe(DFA.Node, state) });
                        }

                        if (!regular_symbols_map.contains(new_top2)) {
                            try regular_symbols_map.put(new_top2, .{ .sym = r.new_top, .state = try gpa.dupe(DFA.Node, newstate) });
                        }

                        try new_rules.append(LabelledRule{
                            .label = lr.label,
                            .rule = Rule{
                                .call = CallRule{
                                    .from = r.from,
                                    .top = top2,
                                    .to = r.to,
                                    .new_top = new_top2,
                                    .new_tail = new_tail2,
                                },
                            },
                        });
                    }
                },
                .ret => |r| {
                    const topstr = proc.symbols.symbol_names.get(r.top).?;

                    for (all_states) |state| {
                        const topstr2 = try std.fmt.allocPrint(proc.arena, "{s}@{any}", .{ topstr, state });
                        const top2 = try proc.process_symbol(topstr2);

                        if (!regular_symbols_map.contains(top2)) {
                            try regular_symbols_map.put(top2, .{ .sym = r.top, .state = try gpa.dupe(DFA.Node, state) });
                        }

                        try new_rules.append(LabelledRule{
                            .label = lr.label,
                            .rule = Rule{
                                .ret = RetRule{
                                    .from = r.from,
                                    .top = top2,
                                    .to = r.to,
                                },
                            },
                        });
                    }
                },
                .sm => {
                    try new_rules.append(lr);
                },
            }
        }

        proc.system.?.rules.clearRetainingCapacity();
        try proc.system.?.rules.appendSlice(new_rules.items);

        for (regular_symbols_map.keys()) |symbol| {
            for (proc.states.state_map.keys()) |name| {
                try state_aps.put(.{ .state = proc.states.state_map.get(name).?, .top = symbol }, std.StringArrayHashMap(void).init(gpa));
            }
        }

        proc.system.?.alphabet = try proc.arena.dupe(Symbol, regular_symbols_map.keys());

        try fillAps(&state_aps, formula, state_names, func);

        val_loop: for (valuations) |val| {
            if (!formula.hasAP(val.ap)) {
                continue;
            }
            switch (val.val) {
                .state => |s| {
                    if (regular_symbols_map.count() > 0) {
                        for (regular_symbols_map.keys()) |symbol| {
                            for (proc.states.state_map.keys()) |state_str| {
                                if (func(s, state_str)) {
                                    const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = symbol }).?;
                                    _ = &ap_set;
                                    try ap_set.*.put(val.ap, {});
                                }
                            }
                        }
                    } else {
                        for (proc.symbols.symbol_map.keys()) |symbol| {
                            for (proc.states.state_map.keys()) |state_str| {
                                if (func(s, state_str)) {
                                    const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = proc.symbols.symbol_map.get(symbol).? }).?;
                                    try ap_set.*.put(val.ap, {});
                                }
                            }
                        }
                    }
                },
                .simple => |s| {
                    if (regular_symbols_map.count() > 0) {
                        for (proc.states.state_map.keys()) |state_str| {
                            if (s.state == null or func(s.state.?, state_str)) {
                                for (regular_symbols_map.keys()) |symbol| {
                                    if (regular_symbols_map.get(symbol).?.sym == (proc.symbols.symbol_map.get(s.top) orelse continue :val_loop)) {
                                        const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = symbol }).?;
                                        try ap_set.*.put(val.ap, {});
                                    }
                                }
                            }
                        }
                    } else {
                        for (proc.states.state_map.keys()) |state_str| {
                            if (s.state == null or func(s.state.?, state_str)) {
                                const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = proc.symbols.symbol_map.get(s.top).? }).?;
                                try ap_set.*.put(val.ap, {});
                            }
                        }
                    }
                },
                .regular => |reg| {
                    for (proc.states.state_map.keys()) |state_str| {
                        if (reg.state == null or func(reg.state.?, state_str)) {
                            for (regular_symbols_map.keys()) |symbol| {
                                const dfa_num = ap_dfas.get(val.ap).?.get(proc.states.state_map.get(state_str).?).?;
                                const sym_pair = regular_symbols_map.get(symbol).?;
                                const dfa_state = sym_pair.state[dfa_num];
                                const fin = dfas.items[dfa_num].finish;
                                const symstr = proc.symbols.symbol_names.get(sym_pair.sym).?;
                                for (dfas.items[dfa_num].edges.items) |edge| {
                                    if (edge.from == dfa_state and std.mem.eql(u8, edge.sym, symstr)) {
                                        for (fin.items) |f| {
                                            if (f == edge.to) {
                                                const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = symbol }).?;
                                                try ap_set.*.put(val.ap, {});
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                },
                // else => {},
            }
        }

        // _ = init_conf;
        if (regular_symbols_map.count() > 0) {
            const prev_state = try dfa_set.getInit(gpa);
            defer gpa.free(prev_state);
            const cur_state = try dfa_set.getInit(gpa);
            defer gpa.free(cur_state);
            var ind = init_conf.stack.len - 1;
            while (ind >= 0) {
                for (regular_symbols_map.keys()) |symbol| {
                    const sym_pair = regular_symbols_map.get(symbol).?;
                    if (sym_pair.sym == init_conf.stack[ind] and std.mem.eql(DFA.Node, sym_pair.state, prev_state)) {
                        init_conf.stack[ind] = symbol;

                        dfa_set.getEdgePrealloced(cur_state, prev_state, proc.symbols.symbol_names.get(sym_pair.sym).?);

                        std.mem.copyBackwards(u32, prev_state, cur_state);
                    }
                }
                if (ind == 0) break;
                ind -= 1;
            }
        }

        return LabellingFunction{
            .state_aps = state_aps,
        };
    }

    pub fn initFromLabels(gpa: std.mem.Allocator, proc: *SM_PDS_Processor, labels: std.StringArrayHashMap([]const []const u8)) !LabellingFunction {
        var state_names = std.AutoHashMap(State, []const u8).init(gpa);
        defer state_names.deinit();
        var state_aps = std.AutoArrayHashMap(State, std.StringArrayHashMap(void)).init(gpa);

        for (proc.states.state_map.keys()) |name| {
            const lb = labels.get(name);
            var ap_set = std.StringArrayHashMap(void).init(gpa);
            if (lb) |lbls| {
                for (lbls) |lbl_name| {
                    try ap_set.put(lbl_name, {});
                }
            }

            for (proc.symbols.symbol_map.keys()) |symbol| {
                try state_aps.put(.{ .state = proc.states.state_map.get(name).?, .top = proc.symbols.symbol_map.get(symbol).? }, ap_set);
            }
        }

        return LabellingFunction{
            .state_aps = state_aps,
        };
    }

    pub fn deinit(self: *@This()) void {
        for (self.state_aps.keys()) |s| {
            self.state_aps.getPtr(s).?.deinit();
        }
        self.state_aps.deinit();
    }

    pub const strict: Labeller = struct {
        pub fn cmp(ap: []const u8, control_point: []const u8) bool {
            return std.mem.eql(u8, ap, control_point);
        }
    }.cmp;

    pub const substr: Labeller = struct {
        pub fn cmp(ap: []const u8, control_point: []const u8) bool {
            return std.mem.indexOf(u8, control_point, ap) != null;
        }
    }.cmp;

    pub const naive: Labeller = struct {
        pub fn cmp(ap: []const u8, control_point: []const u8) bool {
            const delim = std.mem.lastIndexOf(u8, control_point, "#").?;
            // std.debug.print("Comparing {s} and {s}: {}\n", .{ ap, control_point, std.mem.eql(u8, control_point[0..delim], ap) });
            return std.mem.eql(u8, control_point[0..delim], ap);
        }
    }.cmp;

    pub fn fillAps(
        state_aps: *std.AutoArrayHashMap(Key, std.StringArrayHashMap(void)),
        formula: Caret.Formula,
        state_names: std.AutoHashMap(State, []const u8),
        func: Labeller,
    ) !void {
        switch (formula) {
            .at => |at| {
                for (state_aps.keys()) |s| {
                    const name = state_names.get(s.state).?;
                    if (func(at.name, name)) {
                        try state_aps.getPtr(s).?.put(at.name, {});
                    }
                }
            },
            .top, .bot, .trans => {},
            .lnot => |n| {
                try fillAps(state_aps, n.neg, state_names, func);
            },
            .lor => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .xg => |n| {
                try fillAps(state_aps, n.next, state_names, func);
            },
            .xa => |n| {
                try fillAps(state_aps, n.next, state_names, func);
            },
            .xc => |n| {
                try fillAps(state_aps, n.next, state_names, func);
            },
            .ug => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .ua => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
            .uc => |n| {
                try fillAps(state_aps, n.left, state_names, func);
                try fillAps(state_aps, n.right, state_names, func);
            },
        }
    }

    // pub fn isAPinState(self: @This(), ap: []const u8, state: State) bool {
    //     const aps = self.getAPs(state);

    //     return aps.contains(ap);
    // }

    pub fn getAPs(self: @This(), key: Key) std.StringArrayHashMap(void) {
        return self.state_aps.get(key).?;
    }
};

pub const PhaseTriple = struct {
    original_phase: PhaseName,
    to_remove: PhaseName,
    to_add: PhaseName,
};

pub const SM_PDS_Processor = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    rule_names: RuleNameProcessor,
    states: StateProcessor,
    symbols: SymbolProcessor,
    phase_names: PhaseProcessor,

    phase_combiner: std.AutoArrayHashMap(PhaseTriple, PhaseName),
    phases: std.AutoArrayHashMap(PhaseName, void),

    system: ?SM_PDS,

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator) @This() {
        return .{
            .system = null,

            .arena = arena,
            .gpa = gpa,

            .rule_names = RuleNameProcessor.init(arena),
            .states = StateProcessor.init(arena),
            .symbols = SymbolProcessor.init(arena),
            .phase_names = PhaseProcessor.init(arena),
            .phase_combiner = std.AutoArrayHashMap(PhaseTriple, PhaseName).init(gpa),
            .phases = std.AutoArrayHashMap(PhaseName, void).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.phase_combiner.deinit();
        self.phases.deinit();
        if (self.system) |*s| {
            s.rules.deinit();
        }
    }

    pub fn process_state(self: *@This(), state: []const u8) !State {
        return try self.states.get_state_name(state);
    }

    pub fn process_symbol(self: *@This(), symbol: []const u8) !Symbol {
        return try self.symbols.get_symbol_name(symbol);
    }

    pub fn process_rule_name(self: *@This(), rule_name: []const u8) !RuleName {
        return try self.rule_names.get_rule_name(rule_name);
    }

    pub fn process_phase(self: *@This(), phase: []const []const u8) !PhaseName {
        var processed_phase = Set(RuleName){ .items = std.AutoArrayHashMap(RuleName, void).init(self.arena) };
        try processed_phase.items.ensureTotalCapacity(phase.len);
        for (phase) |r| {
            try processed_phase.items.put(try self.process_rule_name(r), {});
        }
        const name = try self.phase_names.get_phase_name(processed_phase);
        return name;
    }

    const ProcessingError = error{
        InvalidRule,
        SameStateInTwoProcesses,
    };

    pub fn process(self: *@This(), smpds: Unprocessed.SM_PDS, init_conf: Unprocessed.Conf) !void {
        var rules = std.ArrayList(LabelledRule).init(self.gpa);

        for (smpds.rules) |rule| {
            const processed_rule: Rule = switch (rule.typ) {
                Unprocessed.RuleType.internal => Rule{ .int = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .top = try self.process_symbol(rule.top orelse return ProcessingError.InvalidRule),
                    .new_top = if (rule.new_top) |_| try self.process_symbol(rule.new_top.?) else null,
                    .new_tail = if (rule.new_tail) |nt| try self.process_symbol(nt) else null,
                } },
                Unprocessed.RuleType.call => Rule{ .call = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .top = try self.process_symbol(rule.top orelse return ProcessingError.InvalidRule),
                    .new_top = try self.process_symbol(rule.new_top orelse return ProcessingError.InvalidRule),
                    .new_tail = try self.process_symbol(rule.new_tail orelse return ProcessingError.InvalidRule),
                } },
                Unprocessed.RuleType.ret => Rule{ .ret = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .top = try self.process_symbol(rule.top orelse return ProcessingError.InvalidRule),
                } },
                Unprocessed.RuleType.sm => Rule{ .sm = .{
                    .from = try self.process_state(rule.from),
                    .to = try self.process_state(rule.to),
                    .old_phase = try self.process_phase(rule.sm_l orelse return ProcessingError.InvalidRule),
                    .new_phase = try self.process_phase(rule.sm_r orelse return ProcessingError.InvalidRule),
                } },
            };
            const name = try self.process_rule_name(rule.name);
            try rules.append(LabelledRule{ .label = name, .rule = processed_rule });
        }

        var states = try self.arena.alloc(State, smpds.states.len);
        for (smpds.states, 0..) |s, j| {
            states[j] = try self.process_state(s);
        }

        var alphabet = try self.arena.alloc(Symbol, smpds.alphabet.len + 1);
        for (smpds.alphabet, 0..) |s, j| {
            alphabet[j] = try self.process_symbol(s);
        }
        alphabet[smpds.alphabet.len] = try self.process_symbol("#");

        self.system = SM_PDS{
            .rules = rules,
            .states = states,
            .alphabet = alphabet,
            .phases = &self.phase_names,
            .end_of_stack = alphabet[smpds.alphabet.len],
            .init_conf = try self.getInit(init_conf),
        };

        const conf = try self.getInit(init_conf);
        _ = try self.getPhases(conf.phase);
    }

    pub fn getInit(self: *@This(), init_conf: Unprocessed.Conf) !Conf {
        const state = try self.process_state(init_conf.state);
        var stack = try self.arena.alloc(Symbol, init_conf.stack.len);
        for (init_conf.stack, 0..) |s, i| {
            stack[i] = try self.process_symbol(s);
        }
        const phase = try self.process_phase(init_conf.phase);
        return Conf{
            .state = state,
            .stack = stack,
            .phase = phase,
        };
    }

    pub fn getPhases(self: *@This(), init_phase: PhaseName) !void {
        var visited_phases = &self.phases;

        var phase_stack = std.ArrayList(PhaseName).init(self.gpa);
        defer phase_stack.deinit();

        try phase_stack.append(init_phase);
        while (phase_stack.pop()) |ph| {
            if (visited_phases.contains(ph)) {
                continue;
            }
            try visited_phases.put(ph, {});

            const phase = self.phase_names.phase_values.get(ph).?;
            rule_loop: for (self.system.?.rules.items) |r_labelled| {
                const r_name = r_labelled.label;
                if (!phase.items.contains(r_name)) continue :rule_loop;

                const rule = r_labelled.rule;
                switch (rule) {
                    .sm => |r| {
                        const old_phase = self.phase_names.phase_values.get(r.old_phase).?;
                        for (old_phase.items.keys()) |old_r| {
                            if (!phase.items.contains(old_r)) continue :rule_loop;
                        }

                        var tmp_phase = Set(RuleName){
                            .items = try phase.items.cloneWithAllocator(self.gpa),
                        };
                        defer tmp_phase.items.deinit();

                        for (old_phase.items.keys()) |old_r| {
                            _ = tmp_phase.items.swapRemove(old_r);
                        }

                        const new_phase = self.phase_names.phase_values.get(r.new_phase).?;
                        for (new_phase.items.keys()) |new_r| {
                            try tmp_phase.items.put(new_r, {});
                        }

                        const result_phase = Set(RuleName){
                            .items = try tmp_phase.items.cloneWithAllocator(self.arena),
                        };

                        const result_phase_name = try self.phase_names.get_phase_name(result_phase);
                        // std.debug.print("{}, {}, {}\n", .{ ph, r.old_phase, r.new_phase });
                        try self.phase_combiner.put(PhaseTriple{ .original_phase = ph, .to_remove = r.old_phase, .to_add = r.new_phase }, result_phase_name);
                        try phase_stack.append(result_phase_name);
                        try visited_phases.put(result_phase_name, {});
                    },
                    else => {},
                }
            }
        }
    }
};

pub const MA = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    edges_by_head: std.AutoHashMap(EdgeHead, std.SinglyLinkedList(*const Edge)),
    edge_set: std.AutoHashMap(Edge, void),

    pub const Node = State;

    pub const EdgeSymbol = Symbol;

    pub const Edge = struct {
        from: Node,
        symbol: EdgeSymbol,
        to: Node,
    };

    const EdgeHead = struct {
        from: Node,
        symbol: ?EdgeSymbol,
    };

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator) @This() {
        return .{
            .arena = arena,
            .gpa = gpa,
            .edges_by_head = std.AutoHashMap(EdgeHead, std.SinglyLinkedList(*const Edge)).init(gpa),
            .edge_set = std.AutoHashMap(Edge, void).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.edges_by_head.deinit();
        self.edge_set.deinit();
    }

    fn storeEdge(self: *@This(), edge: Edge) !*const Edge {
        const new_edge = try self.arena.create(Edge);
        new_edge.* = edge;
        return new_edge;
    }

    pub fn addEdge(self: *@This(), edge: Edge) !bool {
        if (self.edge_set.contains(edge)) {
            return false;
        }
        try self.edge_set.put(edge, {});

        {
            const head = EdgeHead{ .from = edge.from, .symbol = edge.symbol };

            const new_edge = try self.storeEdge(edge);
            const new_node = try self.arena.create(std.SinglyLinkedList(*const Edge).Node);
            new_node.* = std.SinglyLinkedList(*const Edge).Node{
                .data = new_edge,
            };
            const gop = try self.edges_by_head.getOrPut(head);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.SinglyLinkedList(*const Edge){};
            }
            gop.value_ptr.*.prepend(new_node);
        }
        {
            const head = EdgeHead{ .from = edge.from, .symbol = null };

            const new_edge = try self.storeEdge(edge);
            const new_node = try self.arena.create(std.SinglyLinkedList(*const Edge).Node);
            new_node.* = std.SinglyLinkedList(*const Edge).Node{
                .data = new_edge,
            };
            const gop = try self.edges_by_head.getOrPut(head);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.SinglyLinkedList(*const Edge){};
            }
            gop.value_ptr.*.prepend(new_node);
        }
        return true;
    }

    pub const PathResult = struct {
        end_node: Node,
    };

    fn hasPathAux(self: @This(), from: Node, word: []const Symbol, res: *std.AutoArrayHashMap(PathResult, void)) !void {
        if (word.len == 0) {
            try res.put(PathResult{
                .end_node = from,
            }, {});
            return;
        }

        exact_symbols: {
            var edge_list = self.edges_by_head.get(EdgeHead{
                .from = from,
                .symbol = word[0],
            }) orelse break :exact_symbols;
            while (edge_list.popFirst()) |edge_node| {
                try self.hasPathAux(edge_node.data.to, word[1..], res);
            }
        }
    }

    pub fn hasPath(self: @This(), alloc: std.mem.Allocator, from: Node, word: []const Symbol) ![]PathResult {
        var res = std.AutoArrayHashMap(PathResult, void).init(self.gpa);
        defer res.deinit();

        try self.hasPathAux(from, word, &res);
        return try alloc.dupe(PathResult, res.keys());
    }

    pub fn accepts(self: @This(), from: Node, word: []const Symbol) !bool {
        const paths = try self.hasPath(self.gpa, from, word);
        defer self.gpa.free(paths);

        for (paths) |path| {
            switch (path.end_node) {
                .int => |i| {
                    if (i.accepting) return true;
                },
                .st => {},
            }
        }
        return false;
    }

    pub var add_edge_time: usize = 0;
    pub var path_time: usize = 0;
    pub var sm_time: usize = 0;

    fn saturateStep(self: *@This(), arena: std.mem.Allocator, sm_pds: *const SM_PDS_Processor) !usize {
        var path_arena = std.heap.ArenaAllocator.init(arena);
        defer path_arena.deinit();

        var edges_added: usize = 0;

        rule_loop: for (sm_pds.system.?.rules.items) |rule| {
            switch (rule.rule) {
                .int => |r| {
                    _ = path_arena.reset(.retain_capacity);
                    var word: [2]Symbol = undefined;
                    var word_slice: []const Symbol = undefined;
                    if (r.new_top != null and r.new_tail != null) {
                        word = .{ r.new_top.?, r.new_tail.? };
                        word_slice = &word;
                    } else if (r.new_top != null) {
                        word = .{ r.new_top.?, undefined };
                        word_slice = word[0..1];
                    } else {
                        word_slice = word[0..0];
                    }
                    var t = try std.time.Timer.start();
                    const to_node = r.to;

                    const paths = try self.hasPath(path_arena.allocator(), to_node, word_slice);

                    path_time += t.lap();
                    for (paths) |p| {
                        const from_node = r.from;
                        if (try self.addEdge(Edge{
                            .from = from_node,
                            .to = p.end_node,
                            .symbol = r.top,
                        })) {
                            edges_added += 1;
                        }
                        add_edge_time += t.lap();
                    }
                },
                .call => |r| {
                    _ = path_arena.reset(.retain_capacity);
                    var word: [2]Symbol = undefined;
                    var word_slice: []const Symbol = undefined;
                    word = .{ r.new_top, r.new_tail };
                    word_slice = &word;
                    var t = try std.time.Timer.start();
                    const to_node = r.to;

                    const paths = try self.hasPath(path_arena.allocator(), to_node, word_slice);

                    path_time += t.lap();
                    for (paths) |p| {
                        const from_node = r.from;
                        if (try self.addEdge(Edge{
                            .from = from_node,
                            .to = p.end_node,
                            .symbol = r.top,
                        })) {
                            edges_added += 1;
                        }
                        add_edge_time += t.lap();
                    }
                },
                .ret => |r| {
                    _ = path_arena.reset(.retain_capacity);
                    var word: [0]Symbol = undefined;
                    var word_slice: []const Symbol = undefined;
                    word_slice = word[0..0];
                    var t = try std.time.Timer.start();
                    const to_node = r.to;

                    const paths = try self.hasPath(path_arena.allocator(), to_node, word_slice);

                    path_time += t.lap();
                    for (paths) |p| {
                        const from_node = r.from;
                        if (try self.addEdge(Edge{
                            .from = from_node,
                            .to = p.end_node,
                            .symbol = r.top,
                        })) {
                            edges_added += 1;
                        }
                        add_edge_time += t.lap();
                    }
                },
                .sm => |r| {
                    var t = try std.time.Timer.start();
                    const to_node = r.to;
                    var edges = self.edges_by_head.get(EdgeHead{
                        .from = to_node,
                        .symbol = null,
                    }) orelse continue :rule_loop;
                    while (edges.popFirst()) |edge_node| {
                        const edge = edge_node.data;
                        const from_node = r.from;
                        if (try self.addEdge(Edge{
                            .from = from_node,
                            .to = edge.to,
                            .symbol = edge.symbol,
                        })) {
                            edges_added += 1;
                        }
                    }
                    sm_time += t.lap();
                },
            }
        }

        return edges_added;
    }

    pub fn saturate(self: *@This(), sm_pds: *const SM_PDS_Processor) !void {
        var arena = std.heap.ArenaAllocator.init(self.arena);
        defer arena.deinit();

        while (try self.saturateStep(arena.allocator(), sm_pds) > 0) : (_ = arena.reset(.retain_capacity)) {}
    }
};

const StatePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: State,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        try writer.print("{s}", .{self.printer.state_map.get(self.to_print).?});
    }
};

const SymbolPrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: Symbol,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        try writer.print("{s}", .{self.printer.proc.symbols.symbol_names.get(self.to_print).?});
    }
};

const RuleNamePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: RuleName,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        try writer.print("{s}", .{self.printer.rule_map.get(self.to_print).?});
    }
};

const PhasePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: PhaseName,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        const phase = self.printer.proc.phase_names.phase_values.get(self.to_print).?;
        for (phase.items.keys(), 0..) |rn, i| {
            try writer.print("{}", .{self.printer.rulename(rn)});
            if (i < phase.items.count() - 1) {
                try writer.print(", ", .{});
            }
        }
    }
};

const RulePrinter = struct {
    printer: *SM_PDS_Printer,
    to_print: LabelledRule,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        try writer.print("{}: ", .{self.printer.rulename(self.to_print.label)});
        switch (self.to_print.rule) {
            .int => |r| {
                try writer.print("{} {} -int-> {} {?} {?}", .{
                    self.printer.state(r.from),
                    self.printer.symbol(r.top),
                    self.printer.state(r.to),
                    if (r.new_top) |rr| self.printer.symbol(rr) else null,
                    if (r.new_tail) |rr| self.printer.symbol(rr) else null,
                });
            },
            .call => |r| {
                try writer.print("{} {} -call-> {} {} {}", .{
                    self.printer.state(r.from),
                    self.printer.symbol(r.top),
                    self.printer.state(r.to),
                    self.printer.symbol(r.new_top),
                    self.printer.symbol(r.new_tail),
                });
            },

            .ret => |r| {
                try writer.print("{} {} -ret-> {}", .{
                    self.printer.state(r.from),
                    self.printer.symbol(r.top),
                    self.printer.state(r.to),
                });
            },

            .sm => |r| {
                try writer.print("{} -({} / {})-> {}", .{
                    self.printer.state(r.from),
                    self.printer.phase(r.old_phase),
                    self.printer.phase(r.new_phase),
                    self.printer.state(r.to),
                });
            },
        }
    }
};

pub const SM_PDS_Printer = struct {
    proc: *const SM_PDS_Processor,
    state_map: std.AutoHashMap(State, []const u8),
    rule_map: std.AutoHashMap(RuleName, []const u8),

    pub fn init(gpa: std.mem.Allocator, proc: *const SM_PDS_Processor) !SM_PDS_Printer {
        var state_map = std.AutoHashMap(State, []const u8).init(gpa);
        for (proc.states.state_map.keys()) |k| {
            try state_map.put(proc.states.state_map.get(k).?, k);
        }

        var rule_map = std.AutoHashMap(RuleName, []const u8).init(gpa);
        for (proc.rule_names.rule_map.keys()) |k| {
            try rule_map.put(proc.rule_names.rule_map.get(k).?, k);
        }

        return SM_PDS_Printer{
            .proc = proc,
            .state_map = state_map,
            .rule_map = rule_map,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.state_map.deinit();
        self.rule_map.deinit();
    }

    pub fn rulename(self: *@This(), r: RuleName) RuleNamePrinter {
        return RuleNamePrinter{
            .printer = self,
            .to_print = r,
        };
    }

    pub fn state(self: *@This(), s: State) StatePrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }

    pub fn symbol(self: *@This(), s: Symbol) SymbolPrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }

    pub fn phase(self: *@This(), s: PhaseName) PhasePrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }

    pub fn rule(self: *@This(), s: LabelledRule) RulePrinter {
        return .{
            .printer = self,
            .to_print = s,
        };
    }
};

const ProcessResult = struct {
    init: Conf,
    processor: SM_PDS_Processor,
    caret: Caret.Formula,
};

pub fn process(
    allocator: std.mem.Allocator,
    unprocessed_conf: parser.ParsedSMPDS,
    ap_strat: APStrategy,
) !ProcessResult {
    var processor = SM_PDS_Processor.init(allocator);

    const unprocessed = unprocessed_conf.smpds;

    try processor.process(unprocessed);
    const init = try processor.getInit(unprocessed_conf.init);

    const caret = try processCaret(
        allocator,
        unprocessed_conf.caret,
        &processor.states,
        &processor.symbols,
        processor.system.?.end_of_stack,
        ap_strat,
    );

    return ProcessResult{
        .caret = caret,
        .init = init,
        .processor = processor,
    };
}

pub const APStrategy = enum {
    substr,
    eql,
    naive,
    naive_substr,
};

pub fn AMA(comptime S: type) type {
    return struct {
        pub const NodeName = u32;

        var node_name_offset: NodeName = 0;

        pub fn add_node(_: *@This()) NodeName {
            const name = node_name_offset;
            node_name_offset += 1;
            return name;
        }

        pub fn add_init_node(self: *@This(), init: S) !NodeName {
            const name = node_name_offset;
            try self.init_names.put(init, name);
            node_name_offset += 1;
            return name;
        }

        pub const Edge = struct {
            from: NodeName,
            to: []const NodeName,
            symbol: Symbol,
        };

        init_names: std.AutoArrayHashMap(S, NodeName),
        edges: []const Edge,
    };
}

pub const Caret = struct {
    pub const At = struct {
        name: []const u8,
    };

    pub const Lnot = struct {
        neg: Formula,
    };

    pub const Or = struct {
        left: Formula,
        right: Formula,
    };

    pub const Ug = struct {
        left: Formula,
        right: Formula,
    };

    pub const Ua = struct {
        left: Formula,
        right: Formula,
    };

    pub const Uc = struct {
        left: Formula,
        right: Formula,
    };

    pub const Xg = struct {
        next: Formula,
    };

    pub const Xa = struct {
        next: Formula,
    };

    pub const Xc = struct {
        next: Formula,
    };

    pub const Formula = union(enum) {
        pub const TransLabel = enum { call, int, ret };
        at: *const At,
        top: void,
        bot: void,
        trans: TransLabel,
        // land: *const And,
        lnot: *const Lnot,
        lor: *const Or,
        ug: *const Ug,
        ua: *const Ua,
        uc: *const Uc,
        xg: *const Xg,
        xa: *const Xa,
        xc: *const Xc,

        const F = @This();

        pub const ArrayMapContext = struct {
            pub const prime = 1610612741;

            pub fn eql(self: @This(), left: F, right: F, i: usize) bool {
                switch (left) {
                    .at => |a| {
                        return right == .at and std.mem.eql(u8, a.name, right.at.name);
                    },
                    .bot, .top => {
                        return @intFromEnum(left) == @intFromEnum(right);
                    },
                    .trans => |t| {
                        return right == .trans and t == right.trans;
                    },
                    .lnot => |n| {
                        return right == .lnot and self.eql(n.neg, right.lnot.neg, i);
                    },
                    .lor => |n| {
                        return right == .lor and self.eql(n.left, right.lor.left, i) and self.eql(n.right, right.lor.right, i);
                    },
                    .ug => |n| {
                        return right == .ug and self.eql(n.left, right.ug.left, i) and self.eql(n.right, right.ug.right, i);
                    },
                    .ua => |n| {
                        return right == .ua and self.eql(n.left, right.ua.left, i) and self.eql(n.right, right.ua.right, i);
                    },
                    .uc => |n| {
                        return right == .uc and self.eql(n.left, right.uc.left, i) and self.eql(n.right, right.uc.right, i);
                    },
                    .xg => |n| {
                        return right == .xg and self.eql(n.next, right.xg.next, i);
                    },
                    .xa => |n| {
                        return right == .xa and self.eql(n.next, right.xa.next, i);
                    },
                    .xc => |n| {
                        return right == .xc and self.eql(n.next, right.xc.next, i);
                    },
                }
            }

            fn hashAux(self: @This(), f: F, depth: u32) u32 {
                return depth *% blk: switch (f) {
                    .bot, .top => @intFromEnum(f),
                    .trans => |t| {
                        const tt: u32 = @intCast(@intFromEnum(t));
                        break :blk @intFromEnum(f) *% (tt *% prime);
                    },
                    .at => |a| {
                        const str_hash: u32 = @truncate(std.hash_map.hashString(a.name));
                        break :blk @intFromEnum(f) *% (str_hash *% prime);
                    },
                    .lnot => |n| @intFromEnum(f) *% self.hashAux(n.neg, depth *% prime),
                    .lor => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .ug => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .ua => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .uc => |n| @intFromEnum(f) *% self.hashAux(n.left, depth *% prime) *% self.hashAux(n.left, depth *% prime *% prime),
                    .xg => |n| @intFromEnum(f) *% self.hashAux(n.next, depth *% prime),
                    .xa => |n| @intFromEnum(f) *% self.hashAux(n.next, depth *% prime),
                    .xc => |n| @intFromEnum(f) *% self.hashAux(n.next, depth *% prime),
                };
            }

            pub fn hash(self: @This(), f: F) u32 {
                return self.hashAux(f, prime);
            }
        };

        pub fn format(
            self: @This(),
            comptime fmt: []const u8,
            _: std.fmt.FormatOptions,
            writer: anytype,
        ) !void {
            if (fmt.len != 0) {
                std.fmt.invalidFmtError(fmt, self);
            }
            return switch (self) {
                .at => |at| try writer.print("{s}", .{at.name}),
                .top => try writer.print("True", .{}),
                .bot => try writer.print("False", .{}),
                .trans => |t| try writer.print("{s}", .{switch (t) {
                    .call => "call",
                    .int => "int",
                    .ret => "ret",
                }}),
                // .land => |node| try writer.print("{} && {}", .{ node.left, node.right }),
                .lnot => |node| try writer.print("(~ {})", .{node.neg}),
                .lor => |node| try writer.print("({} || {})", .{ node.left, node.right }),
                .ug => |node| try writer.print("({} Ug {})", .{ node.left, node.right }),
                .ua => |node| try writer.print("({} Ua {})", .{ node.left, node.right }),
                .uc => |node| try writer.print("({} Uc {})", .{ node.left, node.right }),
                .xg => |node| try writer.print("(Xg {})", .{node.next}),
                .xa => |node| try writer.print("(Xa {})", .{node.next}),
                .xc => |node| try writer.print("(Xc {})", .{node.next}),
            };
        }

        pub fn clone(self: @This(), alloc: std.mem.Allocator) !Formula {
            return blk: switch (self) {
                .bot, .top, .at, .trans => self,
                .lnot => |n| {
                    const new_node = try alloc.create(Lnot);
                    new_node.* = Lnot{ .neg = try n.neg.clone(alloc) };
                    break :blk Formula{ .lnot = new_node };
                },
                .lor => |n| {
                    const new_node = try alloc.create(Or);
                    new_node.* = Or{ .left = try n.left.clone(alloc), .right = try n.right.clone(alloc) };
                    break :blk Formula{ .lor = new_node };
                },
                .ug => |n| {
                    const new_node = try alloc.create(Ug);
                    new_node.* = Ug{ .left = try n.left.clone(alloc), .right = try n.right.clone(alloc) };
                    break :blk Formula{ .ug = new_node };
                },
                .ua => |n| {
                    const new_node = try alloc.create(Ua);
                    new_node.* = Ua{ .left = try n.left.clone(alloc), .right = try n.right.clone(alloc) };
                    break :blk Formula{ .ua = new_node };
                },
                .uc => |n| {
                    const new_node = try alloc.create(Uc);
                    new_node.* = Uc{ .left = try n.left.clone(alloc), .right = try n.right.clone(alloc) };
                    break :blk Formula{ .uc = new_node };
                },
                .xg => |n| {
                    const new_node = try alloc.create(Xg);
                    new_node.* = Xg{ .next = try n.next.clone(alloc) };
                    break :blk Formula{ .xg = new_node };
                },
                .xa => |n| {
                    const new_node = try alloc.create(Xa);
                    new_node.* = Xa{ .next = try n.next.clone(alloc) };
                    break :blk Formula{ .xa = new_node };
                },
                .xc => |n| {
                    const new_node = try alloc.create(Xc);
                    new_node.* = Xc{ .next = try n.next.clone(alloc) };
                    break :blk Formula{ .xc = new_node };
                },
            };
        }

        pub fn deinit(self: @This(), alloc: std.mem.Allocator) void {
            switch (self) {
                .bot, .top, .at, .trans => return,
                .lnot => |n| {
                    n.neg.deinit(alloc);
                    alloc.destroy(n);
                },
                .lor => |n| {
                    n.left.deinit(alloc);
                    n.right.deinit(alloc);
                    alloc.destroy(n);
                },
                .ug => |n| {
                    n.left.deinit(alloc);
                    n.right.deinit(alloc);
                    alloc.destroy(n);
                },
                .ua => |n| {
                    n.left.deinit(alloc);
                    n.right.deinit(alloc);
                    alloc.destroy(n);
                },
                .uc => |n| {
                    n.left.deinit(alloc);
                    n.right.deinit(alloc);
                    alloc.destroy(n);
                },
                .xg => |n| {
                    n.next.deinit(alloc);
                    alloc.destroy(n);
                },
                .xa => |n| {
                    n.next.deinit(alloc);
                    alloc.destroy(n);
                },
                .xc => |n| {
                    n.next.deinit(alloc);
                    alloc.destroy(n);
                },
            }
        }

        pub fn getClosureAux(
            gpa: std.mem.Allocator,
            formula: Formula,
            closure: *std.ArrayList(Formula),
            visited: *std.ArrayHashMap(Formula, void, ArrayMapContext, false),
            tmp: bool,
        ) !void {
            if (visited.contains(formula)) {
                if (tmp) formula.deinit(gpa);
                return;
            }
            try visited.put(formula, {});

            switch (formula) {
                .top, .bot => {},
                .at, .trans => {
                    try closure.append(try formula.clone(gpa));
                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                // .land => |node| try writer.print("{} && {}", .{ node.left, node.right }),
                .lnot => |node| {
                    try getClosureAux(gpa, node.neg, closure, visited, false);
                    if (tmp) {
                        try closure.append(formula);
                    } else {
                        try closure.append(try formula.clone(gpa));
                    }
                },
                .lor => |node| {
                    try getClosureAux(gpa, node.left, closure, visited, false);
                    try getClosureAux(gpa, node.right, closure, visited, false);
                    try closure.append(try formula.clone(gpa));
                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                .ug => |node| {
                    try getClosureAux(gpa, node.left, closure, visited, false);
                    try getClosureAux(gpa, node.right, closure, visited, false);
                    try closure.append(try formula.clone(gpa));

                    const new_xg = try gpa.create(Xg);
                    new_xg.* = Xg{ .next = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .xg = new_xg }, closure, visited, true);

                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                .ua => |node| {
                    try getClosureAux(gpa, node.left, closure, visited, false);
                    try getClosureAux(gpa, node.right, closure, visited, false);
                    try closure.append(try formula.clone(gpa));

                    const new_xa = try gpa.create(Xa);
                    new_xa.* = Xa{ .next = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .xa = new_xa }, closure, visited, true);

                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                .uc => |node| {
                    try getClosureAux(gpa, node.left, closure, visited, false);
                    try getClosureAux(gpa, node.right, closure, visited, false);
                    try closure.append(try formula.clone(gpa));

                    const new_xc = try gpa.create(Xc);
                    new_xc.* = Xc{ .next = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .xc = new_xc }, closure, visited, true);

                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                .xg => |node| {
                    try getClosureAux(gpa, node.next, closure, visited, false);
                    try closure.append(if (tmp) formula else try formula.clone(gpa));

                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                .xa => |node| {
                    try getClosureAux(gpa, node.next, closure, visited, false);
                    try closure.append(if (tmp) formula else try formula.clone(gpa));

                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
                .xc => |node| {
                    try getClosureAux(gpa, node.next, closure, visited, false);
                    try closure.append(if (tmp) formula else try formula.clone(gpa));

                    const new_not = try gpa.create(Lnot);
                    new_not.* = Lnot{ .neg = try formula.clone(gpa) };
                    try getClosureAux(gpa, Formula{ .lnot = new_not }, closure, visited, true);
                },
            }
        }

        pub fn get_closure(self: @This(), gpa: std.mem.Allocator) ![]const Formula {
            var closure = std.ArrayList(Formula).init(gpa);
            defer closure.deinit();

            var visited = std.ArrayHashMap(Formula, void, ArrayMapContext, false).init(gpa);
            defer {
                visited.deinit();
            }

            const transition_labels: []const Formula = &.{ Formula{ .trans = .call }, Formula{ .trans = .int }, Formula{ .trans = .ret } };
            for (transition_labels) |t| {
                const node = try gpa.create(Lnot);
                node.* = Lnot{ .neg = t };
                try closure.append(t);
                try visited.put(t, {});

                try closure.append(Formula{ .lnot = node });
                try visited.put(Formula{ .lnot = node }, {});
            }

            try getClosureAux(gpa, self, &closure, &visited, false);

            return try closure.toOwnedSlice();
        }

        pub fn hasAP(self: @This(), ap: []const u8) bool {
            return switch (self) {
                .at => |a| std.mem.eql(u8, ap, a.name),
                .lor => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .lnot => |s| s.neg.hasAP(ap),
                .ug => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .ua => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .uc => |s| s.left.hasAP(ap) or s.right.hasAP(ap),
                .xg => |s| s.next.hasAP(ap),
                .xa => |s| s.next.hasAP(ap),
                .xc => |s| s.next.hasAP(ap),
                else => false,
            };
        }
    };
};

pub fn getStateSetFromAP(allocator: std.mem.Allocator, ap_name: []const u8, states: *const StateProcessor, strat: APStrategy) !std.AutoArrayHashMap(State, void) {
    var res = std.AutoArrayHashMap(State, void).init(allocator);
    for (states.state_map.keys()) |state_name| {
        switch (strat) {
            .substr => {
                if (std.mem.indexOf(u8, state_name, ap_name)) |_| {
                    try res.put(states.state_map.get(state_name).?, {});
                }
            },
            .eql => {
                if (std.mem.eql(u8, state_name, ap_name)) {
                    try res.put(states.state_map.get(state_name).?, {});
                }
            },
            .naive => {
                const div_pos = std.mem.lastIndexOf(u8, state_name, "@").?;
                if (std.mem.eql(u8, state_name[0..div_pos], ap_name)) {
                    try res.put(states.state_map.get(state_name).?, {});
                }
            },
            .naive_substr => {
                const div_pos = std.mem.lastIndexOf(u8, state_name, "@").?;
                if (std.mem.indexOf(u8, state_name[0..div_pos], ap_name)) |_| {
                    try res.put(states.state_map.get(state_name).?, {});
                }
            },
        }
    }
    if (res.count() < 1) {
        std.log.info("Did not find states satisifying AP {s} with a strategy {any}\n", .{ ap_name, strat });
    }
    // std.log.info("Found {d} states satisfying AP {s}\n", .{ res.count(), ap_name });
    return res;
}

pub fn processCaretAux(allocator: std.mem.Allocator, caret_raw: *const Unprocessed.RawCaret) !Caret.Formula {
    switch (caret_raw.*) {
        .ap => |ctl_node| {
            const at = try allocator.create(Caret.At);
            at.* = Caret.At{
                .name = try allocator.dupe(u8, ctl_node),
            };

            return Caret.Formula{ .at = at };
        },
        .top => return .top,
        .bot => return .bot,
        .lnot => |ctl_node| {
            const node = try allocator.create(Caret.Lnot);
            node.* = Caret.Lnot{
                .neg = try processCaretAux(allocator, ctl_node),
            };
            return Caret.Formula{ .lnot = node };
        },
        .lor => |ctl_node| {
            const node = try allocator.create(Caret.Or);
            node.* = Caret.Or{
                .left = try processCaretAux(allocator, ctl_node.left),
                .right = try processCaretAux(allocator, ctl_node.right),
            };
            return Caret.Formula{ .lor = node };
        },
        .ug => |ctl_node| {
            const node = try allocator.create(Caret.Ug);
            node.* = Caret.Ug{
                .left = try processCaretAux(allocator, ctl_node.left),
                .right = try processCaretAux(allocator, ctl_node.right),
            };
            return Caret.Formula{ .ug = node };
        },
        .uc => |ctl_node| {
            const node = try allocator.create(Caret.Uc);
            node.* = Caret.Uc{
                .left = try processCaretAux(allocator, ctl_node.left),
                .right = try processCaretAux(allocator, ctl_node.right),
            };
            return Caret.Formula{ .uc = node };
        },
        .ua => |ctl_node| {
            const node = try allocator.create(Caret.Ua);
            node.* = Caret.Ua{
                .left = try processCaretAux(allocator, ctl_node.left),
                .right = try processCaretAux(allocator, ctl_node.right),
            };
            return Caret.Formula{ .ua = node };
        },
        .xg => |ctl_node| {
            const node = try allocator.create(Caret.Xg);
            node.* = Caret.Xg{
                .next = try processCaretAux(allocator, ctl_node),
            };
            return Caret.Formula{ .xg = node };
        },
        .xa => |ctl_node| {
            const node = try allocator.create(Caret.Xa);
            node.* = Caret.Xa{
                .next = try processCaretAux(allocator, ctl_node),
            };
            return Caret.Formula{ .xa = node };
        },
        .xc => |ctl_node| {
            const node = try allocator.create(Caret.Xc);
            node.* = Caret.Xc{
                .next = try processCaretAux(allocator, ctl_node),
            };
            return Caret.Formula{ .xc = node };
        },
    }
}

pub fn processCaret(
    arena: std.mem.Allocator,
    caret_raw: *const Unprocessed.RawCaret,
) !Caret.Formula {
    return processCaretAux(arena, caret_raw);
}

// pub fn preprocessRegex(arena: std.mem.Allocator, gpa: std.mem.Allocator, smpds: parser.ParsedSMPDS) !parser.ParsedSMPDS {
//     var contains_regex: bool = false;
//     for (smpds.caret.valuations) |val| {
//         switch (val.val) {
//             .regular => contains_regex = true,
//         }
//     }
//     if (!contains_regex) {
//         return smpds;
//     }

//     var unique_dfas = std.StringArrayHashMap(DFA).init(gpa);
//     defer unique_dfas.deinit();

//     var aps = std.ArrayList([]const u8).init(gpa);
//     defer aps.deinit();

//     // fillAps(smpds.caret.formula, aps);

//     var emptyDfa = DFA{
//         .max_node = 0,
//         .start = 0,
//         .finish = std.ArrayList(DFA.Node).init(gpa),
//         .edges = std.ArrayList(DFA.Edge).init(gpa),
//     };
// }

pub const DFASet = struct {
    dfas: []const DFA,

    fn allStatesAux(gpa: std.mem.Allocator, variants: []const std.AutoArrayHashMap(DFA.Node, void), res: *std.ArrayList([]const DFA.Node), cur: *std.ArrayList(DFA.Node)) !void {
        if (cur.items.len == variants.len) {
            try res.append(try cur.toOwnedSlice());
            return;
        }
        for (variants[cur.items.len].keys()) |node| {
            var next_cur = try cur.clone();
            try next_cur.append(node);
            try allStatesAux(gpa, variants, res, &next_cur);
        }
        cur.deinit();
    }

    pub fn getAllStates(self: @This(), gpa: std.mem.Allocator) ![][]const DFA.Node {
        const state_sets = try gpa.alloc(std.AutoArrayHashMap(DFA.Node, void), self.dfas.len);
        defer {
            for (state_sets) |*ss| {
                ss.deinit();
            }
            gpa.free(state_sets);
        }
        for (self.dfas, state_sets) |dfa, *state_set| {
            state_set.* = std.AutoArrayHashMap(DFA.Node, void).init(gpa);
            for (dfa.edges.items) |edge| {
                try state_set.put(edge.from, {});
                try state_set.put(edge.to, {});
            }
        }
        var perms = std.ArrayList([]const DFA.Node).init(gpa);
        var dummy = std.ArrayList(DFA.Node).init(gpa);
        try allStatesAux(gpa, state_sets, &perms, &dummy);
        return perms.toOwnedSlice();
    }

    pub fn getEdge(self: @This(), gpa: std.mem.Allocator, from: []const DFA.Node, sym: []const u8) ![]DFA.Node {
        if (from.len != self.dfas.len) {
            unreachable;
        }
        const new_nodes = try gpa.alloc(DFA.Node, self.dfas.len);
        for (self.dfas, from, new_nodes) |dfa, fr, *trg| {
            for (dfa.edges.items) |edge| {
                if (edge.from == fr and std.mem.eql(u8, edge.sym, sym)) {
                    trg.* = edge.to;
                }
            }
        }
        return new_nodes;
    }

    pub fn getEdgePrealloced(self: @This(), buf: []DFA.Node, from: []const DFA.Node, sym: []const u8) void {
        if (from.len != self.dfas.len) {
            unreachable;
        }
        const new_nodes = buf;
        loop1: for (self.dfas, from, new_nodes) |dfa, fr, *trg| {
            for (dfa.edges.items) |edge| {
                if (edge.from == fr and std.mem.eql(u8, edge.sym, sym)) {
                    trg.* = edge.to;
                    continue :loop1;
                }
            }
            unreachable;
        }
    }

    pub fn getInit(self: @This(), gpa: std.mem.Allocator) ![]DFA.Node {
        const new_nodes = try gpa.alloc(DFA.Node, self.dfas.len);
        for (self.dfas, new_nodes) |dfa, *trg| {
            trg.* = dfa.start;
        }
        return new_nodes;
    }
};

pub const DFA = struct {
    pub const Node = u32;
    pub const Edge = struct {
        from: Node,
        sym: []const u8,
        to: Node,
    };

    max_node: Node,
    start: Node,
    finish: std.ArrayList(Node),
    edges: std.ArrayList(Edge),

    pub fn deinit(self: *@This()) void {
        self.finish.deinit();
        self.edges.deinit();
    }

    pub fn add_node(self: *@This()) Node {
        const res = self.max_node;
        self.max_node += 1;
        return res;
    }
};

pub const NFA = struct {
    pub const Node = u32;
    pub const Edge = struct {
        from: Node,
        sym: *const parser.Regex,
        to: Node,
    };

    max_node: Node,
    start: Node,
    finish: Node,
    edges: std.ArrayList(Edge),

    pub fn initFromRegex(gpa: std.mem.Allocator, regex: *const parser.Regex) !NFA {
        var nfa = NFA{
            .max_node = 0,
            .start = 0,
            .finish = 0,
            .edges = std.ArrayList(Edge).init(gpa),
        };
        const node1 = nfa.add_node();
        const node2 = nfa.add_node();
        nfa.start = node1;
        nfa.finish = node2;
        try nfa.edges.append(Edge{
            .from = node1,
            .sym = regex,
            .to = node2,
        });
        return nfa;
    }

    pub fn deinit(self: *@This()) void {
        self.edges.deinit();
    }

    pub fn add_node(self: *@This()) Node {
        const res = self.max_node;
        self.max_node += 1;
        return res;
    }

    pub fn regToNfaStep(self: *@This()) !bool {
        var edge_opt: ?Edge = null;
        for (self.edges.items, 0..) |e, i| {
            switch (e.sym.*) {
                .u, .c, .star => {
                    edge_opt = e;
                    _ = self.edges.swapRemove(i);
                    break;
                },
                else => {},
            }
        }
        if (edge_opt == null) return false;
        const edge = edge_opt.?;
        switch (edge.sym.*) {
            .u => |pair| {
                try self.edges.append(Edge{
                    .from = edge.from,
                    .to = edge.to,
                    .sym = pair.left,
                });
                try self.edges.append(Edge{
                    .from = edge.from,
                    .to = edge.to,
                    .sym = pair.right,
                });
            },
            .c => |pair| {
                const new_node = self.add_node();
                try self.edges.append(Edge{
                    .from = edge.from,
                    .to = new_node,
                    .sym = pair.left,
                });
                try self.edges.append(Edge{
                    .from = new_node,
                    .to = edge.to,
                    .sym = pair.right,
                });
            },
            .star => |reg| {
                var count_left: u32 = 0;
                var count_right: u32 = 0;
                for (self.edges.items) |e| {
                    if (e.from == edge.from) {
                        count_left += 1;
                    }
                    if (e.to == edge.to) {
                        count_right += 1;
                    }
                }
                if (count_left == 0) {
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = edge.from,
                        .sym = reg,
                    });
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = edge.to,
                        .sym = &parser.epsilon,
                    });
                } else if (count_right == 0) {
                    try self.edges.append(Edge{
                        .from = edge.to,
                        .to = edge.to,
                        .sym = reg,
                    });
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = edge.to,
                        .sym = &parser.epsilon,
                    });
                } else {
                    const new_node = self.add_node();
                    try self.edges.append(Edge{
                        .from = edge.from,
                        .to = new_node,
                        .sym = &parser.epsilon,
                    });
                    try self.edges.append(Edge{
                        .from = new_node,
                        .to = edge.to,
                        .sym = &parser.epsilon,
                    });
                    try self.edges.append(Edge{
                        .from = new_node,
                        .to = new_node,
                        .sym = reg,
                    });
                }
            },
            else => unreachable,
        }
        return true;
    }

    pub fn regToNfa(self: *@This()) !void {
        while (try self.regToNfaStep()) {}
    }

    fn hasPathAux(self: @This(), gpa: std.mem.Allocator, from: Node, word: []const []const u8, res: *std.AutoArrayHashMap(Node, void), epsilon_visited: *std.AutoArrayHashMap(Node, void)) !void {
        try epsilon_visited.put(from, {});
        // std.debug.print("Visited {} / ", .{from});
        // for (word) |w| {
        //     std.debug.print("{s} ", .{w});
        // }
        // std.debug.print("\n", .{});

        for (self.edges.items) |edge| {
            if (edge.from == from and !epsilon_visited.contains(edge.to)) {
                switch (edge.sym.*) {
                    .epsilon => {
                        try self.hasPathAux(gpa, edge.to, word, res, epsilon_visited);
                    },
                    else => {},
                }
            }
        }

        if (word.len == 0) {
            try res.put(from, {});
            return;
        }

        for (self.edges.items) |edge| {
            if (edge.from == from) {
                switch (edge.sym.*) {
                    .symbol => |sym| {
                        if (std.mem.eql(u8, sym, word[0])) {
                            var eps_new = std.AutoArrayHashMap(Node, void).init(gpa);
                            defer eps_new.deinit();

                            try self.hasPathAux(gpa, edge.to, word[1..], res, &eps_new);
                        }
                    },
                    .anysymbol => {
                        var eps_new = std.AutoArrayHashMap(Node, void).init(gpa);
                        defer eps_new.deinit();

                        try self.hasPathAux(gpa, edge.to, word[1..], res, &eps_new);
                    },
                    .epsilon => {},
                    else => unreachable,
                }
            }
        }
    }

    pub fn hasPath(self: @This(), gpa: std.mem.Allocator, from: Node, word: []const []const u8) !std.AutoArrayHashMap(Node, void) {
        var res = std.AutoArrayHashMap(Node, void).init(gpa);

        var eps_new = std.AutoArrayHashMap(Node, void).init(gpa);
        defer eps_new.deinit();

        try self.hasPathAux(gpa, from, word, &res, &eps_new);

        return res;
    }

    pub fn reverse(self: *@This()) void {
        for (self.edges.items) |*edge| {
            const tmp = edge.*.from;
            edge.*.from = edge.*.to;
            edge.*.to = tmp;
        }
        const tmp = self.start;
        self.start = self.finish;
        self.finish = tmp;
    }

    pub fn determinize(self: *@This(), gpa: std.mem.Allocator, alphabet: []const []const u8) !DFA {
        const TransitionRow = std.StringArrayHashMap(Node);

        var node_unions = std.ArrayHashMap(Set(Node), Node, SetContext(Node), false).init(gpa);
        defer {
            for (node_unions.keys()) |*k| {
                k.items.deinit();
            }
            node_unions.deinit();
        }

        var node_unions2 = std.AutoArrayHashMap(Node, Set(Node)).init(gpa);
        defer node_unions2.deinit();

        var transition_table = std.AutoArrayHashMap(Node, TransitionRow).init(gpa);
        defer {
            for (transition_table.keys()) |k| {
                transition_table.getPtr(k).?.deinit();
            }
            transition_table.deinit();
        }

        var visited_nodes = Set(Node){ .items = std.AutoArrayHashMap(Node, void).init(gpa) };
        defer visited_nodes.items.deinit();

        var stack = std.ArrayList(Node).init(gpa);
        defer stack.deinit();

        var start_eps = try self.hasPath(gpa, self.start, &.{});
        var new_start = self.start;
        if (start_eps.count() == 1) {
            try stack.append(self.start);
            start_eps.deinit();
        } else if (start_eps.count() > 1) {
            const to_set_s = Set(Node){
                .items = start_eps,
            };
            const gop = try node_unions.getOrPut(to_set_s);
            if (gop.found_existing) {
                unreachable;
            } else {
                const new_node = self.add_node();
                gop.value_ptr.* = new_node;

                try node_unions2.put(new_node, to_set_s);
                try stack.append(new_node);
                new_start = new_node;
            }
        } else {
            unreachable;
        }
        var i: u32 = 0;
        const trap = self.add_node();
        while (stack.pop()) |cur| {
            if (visited_nodes.items.contains(cur)) {
                continue;
            }
            try visited_nodes.items.put(cur, {});

            // if (i > 12) break;
            i += 1;

            // std.debug.print("Node: {}", .{cur});
            // if (node_unions2.get(cur)) |cc| {
            //     std.debug.print("-> {{", .{});
            //     for (cc.items.keys()) |k| {
            //         std.debug.print("{}, ", .{k});
            //     }
            //     std.debug.print("}}", .{});
            // }
            // std.debug.print("\n", .{});

            var cur_set = std.ArrayList(Node).init(gpa);
            defer cur_set.deinit();
            if (node_unions2.contains(cur)) {
                try cur_set.appendSlice(node_unions2.get(cur).?.items.keys());
            } else {
                try cur_set.append(cur);
            }

            var row = TransitionRow.init(gpa);

            for (alphabet) |sym| {
                var to_set = std.AutoArrayHashMap(Node, void).init(gpa);
                defer to_set.deinit();

                for (cur_set.items) |cc| {
                    // std.debug.print("Try {} / {s}:\n", .{ cc, sym });
                    var path = try self.hasPath(gpa, cc, &.{sym});
                    defer path.deinit();

                    for (path.keys()) |k| {
                        try to_set.put(k, {});
                    }
                }

                var next_node: Node = undefined;
                if (to_set.count() == 1) {
                    next_node = to_set.pop().?.key;
                } else if (to_set.count() > 1) {
                    var to_set_s = Set(Node){
                        .items = try to_set.clone(),
                    };
                    const gop = try node_unions.getOrPut(to_set_s);
                    if (gop.found_existing) {
                        next_node = gop.value_ptr.*;
                        to_set_s.items.deinit();
                    } else {
                        const new_node = self.add_node();
                        next_node = new_node;
                        gop.value_ptr.* = new_node;

                        try node_unions2.put(new_node, to_set_s);
                    }
                } else {
                    next_node = trap;
                }

                try row.put(sym, next_node);

                if (!visited_nodes.items.contains(next_node)) {
                    try stack.append(next_node);
                }
            }

            try transition_table.put(cur, row);
        }

        // for (node_unions2.keys()) |k| {
        //     std.debug.print("{} -> {{", .{k});
        //     for (node_unions2.get(k).?.items.keys()) |kk| {
        //         std.debug.print("{}, ", .{kk});
        //     }
        //     std.debug.print("}}\n", .{});
        // }

        var dfa = DFA{
            .max_node = self.max_node,
            .start = new_start,
            .finish = std.ArrayList(DFA.Node).init(gpa),
            .edges = std.ArrayList(DFA.Edge).init(gpa),
        };

        for (transition_table.keys()) |from| {
            for (transition_table.get(from).?.keys()) |sym| {
                try dfa.edges.append(DFA.Edge{
                    .from = from,
                    .sym = sym,
                    .to = transition_table.get(from).?.get(sym).?,
                });
            }
        }

        for (visited_nodes.items.keys()) |node| {
            if (node_unions2.get(node)) |n_set| {
                if (n_set.items.contains(self.finish)) {
                    try dfa.finish.append(node);
                }
            }
        }
        return dfa;
    }
};

test "regex to nfa" {
    const gpa = std.testing.allocator;

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const Regex = parser.Regex;

    // gamma1 + gamma2* + (gamma1 | gamma2)* + .*
    const regex = Regex{
        .c = .{
            .left = &Regex{
                .symbol = "gamma1",
            },
            .right = &Regex{
                .c = .{
                    .left = &Regex{
                        .star = &Regex{
                            .symbol = "gamma2",
                        },
                    },
                    .right = &Regex{
                        .c = .{
                            .left = &Regex{
                                .star = &Regex{
                                    .u = .{ .left = &Regex{
                                        .symbol = "gamma1",
                                    }, .right = &Regex{
                                        .symbol = "gamma2",
                                    } },
                                },
                            },
                            .right = &Regex{
                                .star = &Regex{
                                    .anysymbol = {},
                                },
                            },
                        },
                    },
                },
            },
        },
    };

    var nfa = try NFA.initFromRegex(gpa, &regex);
    defer nfa.deinit();

    try nfa.regToNfa();
    nfa.reverse();

    // for (nfa.edges.items) |e| {
    //     std.debug.print("{} - {} -> {}\n", .{ e.from, e.sym.*, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {}\n", .{ nfa.start, nfa.finish });

    var dfa = try nfa.determinize(gpa, &.{ "gamma1", "gamma2" });
    defer dfa.deinit();

    // for (dfa.edges.items) |e| {
    //     std.debug.print("{} - {s} -> {}\n", .{ e.from, e.sym, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {any}\n", .{ dfa.start, dfa.finish.items });
}

test "regex to nfa 2" {
    const gpa = std.testing.allocator;

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();

    const Regex = parser.Regex;

    // . + gamma2 + .*
    const regex = Regex{
        .c = .{
            .left = &Regex{
                .anysymbol = {},
            },
            .right = &Regex{
                .c = .{
                    .left = &Regex{
                        .symbol = "gamma2",
                    },
                    .right = &Regex{
                        .star = &Regex{
                            .anysymbol = {},
                        },
                    },
                },
            },
        },
    };

    var nfa = try NFA.initFromRegex(gpa, &regex);
    defer nfa.deinit();

    try nfa.regToNfa();
    nfa.reverse();

    // for (nfa.edges.items) |e| {
    //     std.debug.print("{} - {} -> {}\n", .{ e.from, e.sym.*, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {}\n", .{ nfa.start, nfa.finish });

    var dfa = try nfa.determinize(gpa, &.{ "gamma1", "gamma2" });
    defer dfa.deinit();

    // for (dfa.edges.items) |e| {
    //     std.debug.print("{} - {s} -> {}\n", .{ e.from, e.sym, e.to });
    // }
    // std.debug.print("Start: {}\n Finish: {any}\n", .{ dfa.start, dfa.finish.items });
}

test "regex ap" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    StateProcessor.state_name_offset = 0;
    PhaseProcessor.phase_name_offset = 0;
    SymbolProcessor.symbol_name_offset = 0;
    RuleNameProcessor.rule_name_offset = 0;

    var processor = SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer processor.deinit();

    var file = parser.SmpdsFile.open(allocator, "examples/process_test_regex.smpds");
    // var file = parser.SmpdsFile.open(allocator, "tests/true-2.smpds");
    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try processor.process(unprocessed, unprocessed_conf.init);
    var in = try processor.getInit(unprocessed_conf.init);

    const formula = try processCaret(arena.allocator(), unprocessed_conf.caret.formula);

    var lambda = try LabellingFunction.init(gpa, &processor, formula, LabellingFunction.strict, unprocessed_conf.caret.valuations, &in);
    defer lambda.deinit();

    var printer = try SM_PDS_Printer.init(allocator, &processor);
    defer printer.deinit();

    // for (processor.system.?.rules.items) |lr| {
    //     std.debug.print("{}\n", .{printer.rule(lr)});
    // }

    // for (lambda.state_aps.keys()) |pair| {
    //     if (lambda.state_aps.get(pair).?.count() < 1) continue;
    //     std.debug.print("<{}, {}>: ", .{ printer.state(pair.state), printer.symbol(pair.top) });
    //     for (lambda.state_aps.get(pair).?.keys()) |ap| {
    //         std.debug.print("{s}, ", .{ap});
    //     }
    //     std.debug.print("\n", .{});
    // }

    // std.debug.print("Init: {} ", .{printer.state(in.state)});
    // for (in.stack) |sym| {
    //     std.debug.print("{}, ", .{printer.symbol(sym)});
    // }
    // std.debug.print(" # {}\n", .{printer.phase(in.phase)});
}

test "processing" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    StateProcessor.state_name_offset = 0;
    PhaseProcessor.phase_name_offset = 0;
    SymbolProcessor.symbol_name_offset = 0;
    RuleNameProcessor.rule_name_offset = 0;

    var processor = SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer processor.deinit();

    var file = parser.SmpdsFile.open(allocator, "examples/process_test.smpds");
    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try processor.process(unprocessed, unprocessed_conf.init);
    _ = try processor.getInit(unprocessed_conf.init);

    try std.testing.expectEqual(3, processor.states.state_map.count());
    try std.testing.expectEqual(0, processor.states.state_map.get("p1").?);
    try std.testing.expectEqual(1, processor.states.state_map.get("p2").?);
    try std.testing.expectEqual(2, processor.states.state_map.get("p3").?);

    try std.testing.expectEqual(6, processor.rule_names.rule_map.count());
    try std.testing.expectEqual(0, processor.rule_names.rule_map.get("r1").?);
    try std.testing.expectEqual(1, processor.rule_names.rule_map.get("r2").?);
    try std.testing.expectEqual(2, processor.rule_names.rule_map.get("r3").?);
    try std.testing.expectEqual(3, processor.rule_names.rule_map.get("r4").?);
    try std.testing.expectEqual(4, processor.rule_names.rule_map.get("r5").?);
    try std.testing.expectEqual(5, processor.rule_names.rule_map.get("r6").?);

    try std.testing.expectEqual(3, processor.symbols.symbol_map.count());
    try std.testing.expectEqual(0, processor.symbols.symbol_map.get("g1").?);
    try std.testing.expectEqual(1, processor.symbols.symbol_map.get("g2").?);
    try std.testing.expectEqual(2, processor.symbols.symbol_map.get("#").?);

    try std.testing.expectEqual(4, processor.system.?.phases.phase_values.count());
    try std.testing.expectEqual(1, processor.system.?.phases.phase_values.get(0).?.items.count());
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(0).?.items.get(0).?);
    try std.testing.expectEqual(1, processor.system.?.phases.phase_values.get(1).?.items.count());
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(1).?.items.get(2).?);
    try std.testing.expectEqual(3, processor.system.?.phases.phase_values.get(2).?.items.count());
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(2).?.items.get(0).?);
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(2).?.items.get(1).?);
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(2).?.items.get(2).?);
    try std.testing.expectEqual(2, processor.system.?.phases.phase_values.get(3).?.items.count());
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(3).?.items.get(1).?);
    try std.testing.expectEqual({}, processor.system.?.phases.phase_values.get(3).?.items.get(2).?);

    try std.testing.expectEqual(6, processor.system.?.rules.items.len);
    try std.testing.expectEqualDeep(LabelledRule{
        .label = 0,
        .rule = Rule{
            .int = InternalRule{
                .from = 0,
                .top = 0,
                .to = 1,
                .new_top = 1,
                .new_tail = 0,
            },
        },
    }, processor.system.?.rules.items[0]);

    try std.testing.expectEqualDeep(LabelledRule{
        .label = 1,
        .rule = Rule{
            .call = CallRule{
                .from = 0,
                .top = 0,
                .to = 1,
                .new_top = 1,
                .new_tail = 0,
            },
        },
    }, processor.system.?.rules.items[1]);

    try std.testing.expectEqualDeep(LabelledRule{
        .label = 2,
        .rule = Rule{
            .sm = SMRule{
                .from = 2,
                .to = 2,
                .old_phase = 0,
                .new_phase = 1,
            },
        },
    }, processor.system.?.rules.items[2]);

    try std.testing.expectEqualDeep(LabelledRule{
        .label = 3,
        .rule = Rule{
            .int = InternalRule{
                .from = 2,
                .top = 1,
                .to = 2,
                .new_top = 1,
                .new_tail = null,
            },
        },
    }, processor.system.?.rules.items[3]);

    try std.testing.expectEqualDeep(LabelledRule{
        .label = 4,
        .rule = Rule{
            .int = InternalRule{
                .from = 2,
                .top = 1,
                .to = 2,
                .new_top = null,
                .new_tail = null,
            },
        },
    }, processor.system.?.rules.items[4]);

    try std.testing.expectEqualDeep(LabelledRule{
        .label = 5,
        .rule = Rule{
            .ret = RetRule{
                .from = 2,
                .top = 1,
                .to = 2,
            },
        },
    }, processor.system.?.rules.items[5]);
}

test "caret process" {
    {
        var alloc = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer alloc.deinit();
        const unproc = Unprocessed.RawCaret{ .ap = "at" };
        const correct = Caret.Formula{ .at = &Caret.At{ .name = "at" } };
        try std.testing.expectEqualDeep(correct, processCaret(alloc.allocator(), &unproc));
    }
    {
        var alloc = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer alloc.deinit();
        const unproc = Unprocessed.RawCaret{
            .ug = .{
                .left = &Unprocessed.RawCaret{ .top = {} },
                .right = &Unprocessed.RawCaret{
                    .xa = &Unprocessed.RawCaret{
                        .ap = "123",
                    },
                },
            },
        };
        const correct = Caret.Formula{
            .ug = &Caret.Ug{
                .left = Caret.Formula{ .top = {} },
                .right = Caret.Formula{
                    .xa = &Caret.Xa{
                        .next = Caret.Formula{
                            .at = &Caret.At{ .name = "123" },
                        },
                    },
                },
            },
        };
        try std.testing.expectEqualDeep(correct, processCaret(alloc.allocator(), &unproc));
    }
}

test "closure" {
    {
        const alloc = std.testing.allocator;

        const formula = Caret.Formula{
            .ug = &Caret.Ug{
                .left = Caret.Formula{ .top = {} },
                .right = Caret.Formula{
                    .xa = &Caret.Xa{
                        .next = Caret.Formula{
                            .at = &Caret.At{ .name = "123" },
                        },
                    },
                },
            },
        };

        const cl = try formula.get_closure(alloc);
        defer {
            for (cl) |f| {
                f.deinit(alloc);
            }
            alloc.free(cl);
        }

        // for (cl) |f| {
        //     std.debug.print("{}\n", .{f});
        // }
        try std.testing.expectEqual(14, cl.len);
    }
}
