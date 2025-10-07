const Unprocessed = @import("parser.zig");
const std = @import("std");
const parser = @import("parser.zig");

pub const State = u32;
pub const Symbol = u32;
pub const RuleName = u32;
pub const PhaseName = u32;
pub const Conf = struct {
    state: State,
    stack: []const Symbol,
    phase: PhaseName,
};

pub const InternalRule = struct { from: State, top: Symbol, to: State, new_top: ?Symbol, new_tail: ?Symbol };

pub const CallRule = struct { from: State, top: Symbol, to: State, new_top: Symbol, new_tail: Symbol };

pub const RetRule = struct { from: State, top: Symbol, to: State };

pub const SMRule = struct { from: State, old_phase: PhaseName, new_phase: PhaseName, to: State };

pub const Rule = union(enum) { int: InternalRule, call: CallRule, ret: RetRule, sm: SMRule };

pub fn Pair(comptime F: type, comptime S: type) type {
    return struct {
        first: F,
        second: S,
    };
}

pub const SM_PDS = struct {
    states: []const State,
    alphabet: []const Symbol,
    rules: std.AutoArrayHashMap(RuleName, Rule),
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
    var symbol_name_offset: Symbol = 0;

    pub fn init(allocator: std.mem.Allocator) @This() {
        return .{ .symbol_map = std.StringArrayHashMap(Symbol).init(allocator) };
    }

    pub fn get_symbol_name(self: *@This(), label: []const u8) !Symbol {
        return self.symbol_map.get(label) orelse blk: {
            const name = symbol_name_offset;
            symbol_name_offset += 1;
            try self.symbol_map.put(label, name);
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

    pub fn init(gpa: std.mem.Allocator, proc: *SM_PDS_Processor, formula: Caret.Formula, func: Labeller, valuations: []const parser.Valuation) !LabellingFunction {
        var state_names = std.AutoHashMap(State, []const u8).init(gpa);
        defer state_names.deinit();
        var state_aps = std.AutoArrayHashMap(Key, std.StringArrayHashMap(void)).init(gpa);

        for (proc.states.state_map.keys()) |name| {
            try state_names.put(proc.states.state_map.get(name).?, name);
            for (proc.symbols.symbol_map.keys()) |symbol| {
                try state_aps.put(.{ .state = proc.states.state_map.get(name).?, .top = proc.symbols.symbol_map.get(symbol).? }, std.StringArrayHashMap(void).init(gpa));
            }
        }

        try fillAps(&state_aps, formula, state_names, func);

        for (valuations) |val| {
            switch (val.val) {
                .state => |s| {
                    for (proc.symbols.symbol_map.keys()) |symbol| {
                        for (proc.states.state_map.keys()) |state_str| {
                            if (func(s, state_str)) {
                                const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = proc.symbols.symbol_map.get(symbol).? }).?;
                                try ap_set.*.put(val.ap, {});
                            }
                        }
                    }
                },
                .simple => |s| {
                    for (proc.states.state_map.keys()) |state_str| {
                        if (func(s.state, state_str)) {
                            const ap_set = state_aps.getPtr(.{ .state = proc.states.state_map.get(state_str).?, .top = proc.symbols.symbol_map.get(s.top).? }).?;
                            try ap_set.*.put(val.ap, {});
                        }
                    }
                },
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

    phase_combiner: std.AutoHashMap(PhaseTriple, PhaseName),
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
            .phase_combiner = std.AutoHashMap(PhaseTriple, PhaseName).init(gpa),
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
        var rules = std.AutoArrayHashMap(RuleName, Rule).init(self.gpa);

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
            try rules.put(name, processed_rule);
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
            rule_loop: for (self.system.?.rules.keys()) |r_name| {
                if (!phase.items.contains(r_name)) continue :rule_loop;

                const rule = self.system.?.rules.get(r_name).?;
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

pub const NFA = struct {
    pub const Node = u32;
    pub const Edge = struct {
        from: Node,
        sym: []const u8,
        to: Node,
    };
};

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

    try std.testing.expectEqual(6, processor.system.?.rules.count());
    try std.testing.expectEqualDeep(Rule{
        .int = InternalRule{
            .from = 0,
            .top = 0,
            .to = 1,
            .new_top = 1,
            .new_tail = 0,
        },
    }, processor.system.?.rules.get(0));

    try std.testing.expectEqualDeep(Rule{
        .call = CallRule{
            .from = 0,
            .top = 0,
            .to = 1,
            .new_top = 1,
            .new_tail = 0,
        },
    }, processor.system.?.rules.get(1));

    try std.testing.expectEqualDeep(Rule{
        .sm = SMRule{
            .from = 2,
            .to = 2,
            .old_phase = 0,
            .new_phase = 1,
        },
    }, processor.system.?.rules.get(2));

    try std.testing.expectEqualDeep(Rule{
        .int = InternalRule{
            .from = 2,
            .top = 1,
            .to = 2,
            .new_top = 1,
            .new_tail = null,
        },
    }, processor.system.?.rules.get(3));

    try std.testing.expectEqualDeep(Rule{
        .int = InternalRule{
            .from = 2,
            .top = 1,
            .to = 2,
            .new_top = null,
            .new_tail = null,
        },
    }, processor.system.?.rules.get(4));

    try std.testing.expectEqualDeep(Rule{
        .ret = RetRule{
            .from = 2,
            .top = 1,
            .to = 2,
        },
    }, processor.system.?.rules.get(5));
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
