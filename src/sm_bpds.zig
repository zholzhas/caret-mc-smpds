pub const general = @import("gbuchi.zig");
pub const processor = @import("processor.zig");
pub const std = @import("std");

pub const SymbolName = general.SymbolName;
pub const PhaseName = general.PhaseName;
pub const Symbol = general.Symbol;

pub const State = struct {
    general: general.State,
    counter: u8,
};

pub const StandardRule = packed struct {
    label: processor.RuleName,
    from: StateName,
    to: StateName,
    top: SymbolName,
    new_top: ?SymbolName,
    new_tail: ?SymbolName,
};

pub const SMRule = packed struct {
    label: processor.RuleName,
    from: StateName,
    to: StateName,
    old_rules: PhaseName,
    new_rules: PhaseName,
};

pub const Rule = union(enum) {
    standard: StandardRule,
    sm: SMRule,
};

pub const StateName = *const State;

pub const SM_BPDS_Processor = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    sm_gbpds: *general.SM_GBPDS_Processor,

    states: std.SinglyLinkedList(State),
    state_names: std.AutoArrayHashMap(State, StateName),

    rules: std.AutoArrayHashMap(Rule, void),

    pub fn init(gpa: std.mem.Allocator, arena: std.mem.Allocator, sm_gbpds: *general.SM_GBPDS_Processor) SM_BPDS_Processor {
        return SM_BPDS_Processor{
            .gpa = gpa,
            .arena = arena,

            .sm_gbpds = sm_gbpds,

            .states = std.SinglyLinkedList(State){},
            .state_names = std.AutoArrayHashMap(State, StateName).init(gpa),

            .rules = std.AutoArrayHashMap(Rule, void).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.state_names.deinit();
        self.rules.deinit();
    }

    pub fn getStateName(self: *@This(), state: State) !StateName {
        const gop = try self.state_names.getOrPut(state);
        if (gop.found_existing) {
            return gop.value_ptr.*;
        } else {
            const node = try self.arena.create(std.SinglyLinkedList(State).Node);
            node.* = .{ .data = state };
            self.states.prepend(node);
            gop.value_ptr.* = &node.data;
            return &node.data;
        }
    }

    pub fn storeRule(self: *@This(), rule: Rule) !void {
        try self.rules.put(rule, {});
    }

    pub fn isIthAcceptState(self: @This(), state: general.State, i: u8) bool {
        if (i == 0) {
            return state.label == .unexit;
        } else {
            const atoms = self.sm_gbpds.accept_atoms[i - 1];
            const acc_type = atoms.get(state.atom) orelse return false;
            return (acc_type != .unexit) or state.label == .unexit;
        }
    }

    pub fn getMaxI(self: @This()) u8 {
        return @as(u8, @truncate(self.sm_gbpds.accept_atoms.len + 1));
    }

    pub fn next(self: @This(), state: general.State, i: u8) u8 {
        var new_i: u8 = if (i == self.getMaxI()) 0 else i;
        while (new_i < self.getMaxI() and self.isIthAcceptState(state, new_i)) {
            new_i += 1;
        }
        return new_i;
    }

    pub fn isAccepting(self: @This(), state: State) bool {
        return state.counter == self.getMaxI();
    }

    pub fn construct(self: *@This()) !void {
        for (self.sm_gbpds.rule_set.keys()) |rule| {
            switch (rule) {
                .standard => |r| {
                    var i: u8 = 0;
                    while (i <= self.getMaxI()) : (i += 1) {
                        const new_rule = StandardRule{
                            .from = try self.getStateName(State{
                                .general = r.from.*,
                                .counter = i,
                            }),
                            .to = try self.getStateName(State{
                                .general = r.to.*,
                                .counter = self.next(r.to.*, i),
                            }),
                            .label = r.label,
                            .top = r.top,
                            .new_top = r.new_top,
                            .new_tail = r.new_tail,
                        };
                        try self.storeRule(Rule{ .standard = new_rule });
                    }
                },
                .sm => |r| {
                    var i: u8 = 0;
                    while (i <= self.getMaxI()) : (i += 1) {
                        const new_rule = SMRule{
                            .from = try self.getStateName(State{
                                .general = r.from.*,
                                .counter = i,
                            }),
                            .to = try self.getStateName(State{
                                .general = r.to.*,
                                .counter = self.next(r.to.*, i),
                            }),
                            .label = r.label,
                            .old_rules = r.old_rules,
                            .new_rules = r.new_rules,
                        };
                        try self.storeRule(Rule{ .sm = new_rule });
                    }
                },
            }
        }
    }

    pub fn simplify(self: *@This(), inits: []const StateName) !void {
        var arena = std.heap.ArenaAllocator.init(self.arena);
        defer arena.deinit();

        while (try self.simplifyStep(arena.allocator(), inits) > 0) : (_ = arena.reset(.retain_capacity)) {}
    }

    fn simplifyStep(self: *@This(), arena: std.mem.Allocator, inits: []const StateName) !u32 {
        var deleted: u32 = 0;
        var srcs_used = std.AutoHashMap(StateName, void).init(arena);
        defer srcs_used.deinit();

        var trg_used = std.AutoHashMap(StateName, void).init(arena);
        defer trg_used.deinit();

        for (inits) |i| {
            try trg_used.put(i, {});
        }

        for (self.rules.keys()) |rule| {
            switch (rule) {
                .standard => |r| {
                    if (r.top.* == .ret) continue;
                    try srcs_used.put(r.from, {});
                    try trg_used.put(r.to, {});
                },
                .sm => |r| {
                    if (r.from == r.to) continue;
                    try srcs_used.put(r.from, {});
                    try trg_used.put(r.to, {});
                },
            }
        }

        var to_del = std.ArrayList(Rule).init(arena);
        defer to_del.deinit();

        for (self.rules.keys()) |rule| {
            switch (rule) {
                .standard => |r| {
                    if (!srcs_used.contains(r.to) or !trg_used.contains(r.from)) {
                        try to_del.append(rule);
                    }
                },
                .sm => |r| {
                    if (!srcs_used.contains(r.to) or !trg_used.contains(r.from)) {
                        try to_del.append(rule);
                    }
                },
            }
        }

        for (to_del.items) |r| {
            if (self.rules.swapRemove(r)) {
                deleted += 1;
            }
        }
        return deleted;
    }
};

pub const StatePrinter = struct {
    printer: SM_BPDS_Printer,
    state: State,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        try writer.print("{}#{}", .{ self.printer.gen.state(self.state.general), self.state.counter });
    }
};

pub const RulePrinter = struct {
    printer: SM_BPDS_Printer,
    rule: Rule,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        switch (self.rule) {
            .standard => |rule| {
                if (rule.new_tail != null and rule.new_top != null) {
                    try writer.print("{s}: {} {} -> {} {} {}", .{
                        self.printer.gen.rule_names.get(rule.label).?,
                        self.printer.state(rule.from.*),
                        self.printer.gen.symbol(rule.top.*),
                        self.printer.state(rule.to.*),
                        self.printer.gen.symbol(rule.new_top.?.*),
                        self.printer.gen.symbol(rule.new_tail.?.*),
                    });
                } else if (rule.new_top != null) {
                    try writer.print("{s}: {} {} -> {} {}", .{
                        self.printer.gen.rule_names.get(rule.label).?,
                        self.printer.state(rule.from.*),
                        self.printer.gen.symbol(rule.top.*),
                        self.printer.state(rule.to.*),
                        self.printer.gen.symbol(rule.new_top.?.*),
                    });
                } else {
                    try writer.print("{s}: {} {} -> {}", .{
                        self.printer.gen.rule_names.get(rule.label).?,
                        self.printer.state(rule.from.*),
                        self.printer.gen.symbol(rule.top.*),
                        self.printer.state(rule.to.*),
                    });
                }
            },
            .sm => |rule| {
                try writer.print("{s}: {} -({} / {})-> {}", .{
                    self.printer.gen.rule_names.get(rule.label).?,
                    self.printer.state(rule.from.*),
                    self.printer.gen.phase(rule.old_rules),
                    self.printer.gen.phase(rule.new_rules),
                    self.printer.state(rule.to.*),
                });
            },
        }
    }
};

pub const SM_BPDS_Printer = struct {
    gen: *general.SM_GBPDS_Printer,

    pub fn init(gen: *general.SM_GBPDS_Printer) SM_BPDS_Printer {
        return SM_BPDS_Printer{
            .gen = gen,
        };
    }

    pub fn rule(self: @This(), r: Rule) RulePrinter {
        return RulePrinter{
            .printer = self,
            .rule = r,
        };
    }

    pub fn state(self: @This(), s: State) StatePrinter {
        return StatePrinter{
            .printer = self,
            .state = s,
        };
    }
};

pub const MA = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    edges_by_head: std.AutoHashMap(EdgeHead, std.AutoArrayHashMap(*const Edge, void)),
    edge_storage: std.AutoHashMap(Edge, *Edge),
    edge_set: std.AutoHashMap(*const Edge, void),

    pub const StateNode = struct {
        state: StateName,
        phase: PhaseName,
    };

    pub const InternalNode = struct {
        id: u32,
        accepting: bool,
    };

    pub const Node = union(enum) {
        int: InternalNode,
        st: StateNode,
    };

    pub const EdgeSymbol = union(enum) {
        symbol: SymbolName,
        star: void,
    };

    pub const Edge = struct {
        from: Node,
        symbol: EdgeSymbol,
        accepting: bool,
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
            .edges_by_head = std.AutoHashMap(EdgeHead, std.AutoArrayHashMap(*const Edge, void)).init(gpa),
            .edge_set = std.AutoHashMap(*const Edge, void).init(gpa),
            .edge_storage = std.AutoHashMap(Edge, *Edge).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        var it = self.edges_by_head.iterator();
        while (it.next()) |itt| {
            itt.value_ptr.deinit();
        }
        self.edges_by_head.deinit();
        self.edge_set.deinit();
        self.edge_storage.deinit();
    }

    pub fn storeEdge(self: *@This(), edge: Edge) !*const Edge {
        const gop = try self.edge_storage.getOrPut(edge);
        if (gop.found_existing) {
            return gop.value_ptr.*;
        }
        const new_edge = try self.arena.create(Edge);
        new_edge.* = edge;
        gop.value_ptr.* = new_edge;
        return new_edge;
    }

    pub fn addEdgePtr(self: *@This(), new_edge: *const Edge) !bool {
        if (self.edge_set.contains(new_edge)) {
            return false;
        }
        try self.edge_set.put(new_edge, {});
        const edge = new_edge.*;

        {
            const head = EdgeHead{ .from = edge.from, .symbol = edge.symbol };

            const gop = try self.edges_by_head.getOrPut(head);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(new_edge, {});
        }
        {
            const head = EdgeHead{ .from = edge.from, .symbol = null };

            const gop = try self.edges_by_head.getOrPut(head);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(new_edge, {});
        }
        return true;
    }

    pub fn addEdge(self: *@This(), edge: Edge) !bool {
        const new_edge = try self.storeEdge(edge);
        return self.addEdgePtr(new_edge);
    }

    pub const PathResult = struct {
        end_node: Node,
        accepting: bool,
    };

    fn hasPathAux(self: @This(), from: Node, word: []const SymbolName, accepting: bool, res: *std.AutoArrayHashMap(PathResult, void)) !void {
        if (word.len == 0) {
            try res.put(PathResult{
                .end_node = from,
                .accepting = accepting,
            }, {});
            return;
        }

        exact_symbols: {
            var edge_list = self.edges_by_head.get(EdgeHead{
                .from = from,
                .symbol = EdgeSymbol{ .symbol = word[0] },
            }) orelse break :exact_symbols;
            for (edge_list.keys()) |edge| {
                try self.hasPathAux(edge.to, word[1..], accepting or edge.accepting, res);
            }
        }

        star_symbols: {
            var edge_list = self.edges_by_head.get(EdgeHead{
                .from = from,
                .symbol = EdgeSymbol{ .star = {} },
            }) orelse break :star_symbols;
            for (edge_list.keys()) |edge| {
                try self.hasPathAux(edge.to, word[1..], accepting or edge.accepting, res);
            }
        }
    }

    pub fn hasPath(self: @This(), alloc: std.mem.Allocator, from: Node, word: []const SymbolName) ![]PathResult {
        var res = std.AutoArrayHashMap(PathResult, void).init(self.gpa);
        defer res.deinit();

        try self.hasPathAux(from, word, false, &res);
        return try alloc.dupe(PathResult, res.keys());
    }

    pub fn accepts(self: @This(), from: Node, word: []const SymbolName) !bool {
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

    fn saturateStep(self: *@This(), arena: std.mem.Allocator, sm_bpds: *const SM_BPDS_Processor, with_accept: bool) !usize {
        var path_arena = std.heap.ArenaAllocator.init(arena);
        defer path_arena.deinit();

        var edges_added: usize = 0;

        for (sm_bpds.sm_gbpds.sm_pds_proc.?.phases.keys()) |phase_name| {
            const phase = sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(phase_name).?;

            rule_loop: for (sm_bpds.rules.keys()) |rule| {
                const label = switch (rule) {
                    .standard => |r| r.label,
                    .sm => |r| r.label,
                };

                if (!phase.items.contains(label)) {
                    continue;
                }

                switch (rule) {
                    .standard => |r| {
                        _ = path_arena.reset(.retain_capacity);
                        var word: [2]SymbolName = undefined;
                        var word_slice: []const SymbolName = undefined;
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
                        const to_node = Node{ .st = StateNode{
                            .state = r.to,
                            .phase = phase_name,
                        } };

                        if (with_accept and word_slice.len == 0 and !self.edges_by_head.contains(EdgeHead{ .from = to_node, .symbol = null })) {
                            continue :rule_loop;
                        }

                        const paths = try self.hasPath(path_arena.allocator(), to_node, word_slice);

                        path_time += t.lap();
                        for (paths) |p| {
                            const from_node = Node{ .st = StateNode{
                                .state = r.from,
                                .phase = phase_name,
                            } };
                            if (try self.addEdge(Edge{
                                .from = from_node,
                                .to = p.end_node,
                                .symbol = EdgeSymbol{ .symbol = r.top },
                                .accepting = !with_accept and (p.accepting or sm_bpds.isAccepting(r.from.*)),
                            })) {
                                edges_added += 1;
                            }
                            add_edge_time += t.lap();
                        }
                    },
                    .sm => |r| {
                        var t = try std.time.Timer.start();
                        const res_phase = sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.get(.{ .original_phase = phase_name, .to_add = r.new_rules, .to_remove = r.old_rules }) orelse continue :rule_loop;
                        const to_node = Node{ .st = StateNode{
                            .state = r.to,
                            .phase = res_phase,
                        } };
                        var edges = self.edges_by_head.get(EdgeHead{
                            .from = to_node,
                            .symbol = null,
                        }) orelse continue :rule_loop;
                        for (edges.keys()) |edge| {
                            // const edge = edge_node.data;
                            const from_node = Node{ .st = StateNode{
                                .state = r.from,
                                .phase = phase_name,
                            } };
                            if (try self.addEdge(Edge{
                                .from = from_node,
                                .to = edge.to,
                                .symbol = edge.symbol,
                                .accepting = !with_accept and (edge.accepting or sm_bpds.isAccepting(r.from.*)),
                            })) {
                                edges_added += 1;
                            }
                        }
                        sm_time += t.lap();
                    },
                }
            }
        }
        return edges_added;
    }

    pub fn saturate(self: *@This(), sm_bpds: *const SM_BPDS_Processor, with_accept: bool) !void {
        var arena = std.heap.ArenaAllocator.init(self.arena);
        defer arena.deinit();

        while (try self.saturateStep(arena.allocator(), sm_bpds, with_accept) > 0) : (_ = arena.reset(.retain_capacity)) {}
    }

    pub const Printer = struct {
        const Parent = @This();

        gen: *SM_BPDS_Printer,
        pub fn init(gen: *SM_BPDS_Printer) Printer {
            return Printer{
                .gen = gen,
            };
        }

        pub const NodePrinter = struct {
            printer: *Parent,
            node: Node,

            pub fn format(
                self: @This(),
                comptime fmt: []const u8,
                _: std.fmt.FormatOptions,
                writer: anytype,
            ) !void {
                if (fmt.len != 0) {
                    std.fmt.invalidFmtError(fmt, self);
                }
                switch (self.node) {
                    .int => |s| {
                        try writer.print("{s}{}", .{ if (s.accepting) "@" else "/", s.id });
                    },
                    .st => |s| {
                        try writer.print("({}, {})", .{ self.printer.gen.state(s.state.*), self.printer.gen.gen.phase(s.phase) });
                    },
                }
            }
        };

        pub fn node(self: *@This(), n: Node) NodePrinter {
            return .{
                .printer = self,
                .node = n,
            };
        }

        pub const EdgePrinter = struct {
            printer: *Parent,
            edge: Edge,

            pub fn format(
                self: @This(),
                comptime fmt: []const u8,
                _: std.fmt.FormatOptions,
                writer: anytype,
            ) !void {
                if (fmt.len != 0) {
                    std.fmt.invalidFmtError(fmt, self);
                }
                try writer.print("{} -[", .{self.printer.node(self.edge.from)});
                switch (self.edge.symbol) {
                    .symbol => |s| {
                        try writer.print("{}", .{self.printer.gen.gen.symbol(s.*)});
                    },
                    .star => {
                        try writer.print("*", .{});
                    },
                }
                try writer.print("]->{s} {}", .{ if (self.edge.accepting) ">" else "", self.printer.node(self.edge.to) });
            }
        };

        pub fn edge(self: *@This(), e: Edge) EdgePrinter {
            return .{
                .printer = self,
                .edge = e,
            };
        }
    };
};
