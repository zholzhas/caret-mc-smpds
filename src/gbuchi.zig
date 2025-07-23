const processor = @import("processor.zig");
const std = @import("std");

const Formula = processor.Caret.Formula;

pub const Atom = struct {
    const FormulaSet = struct {
        items: std.ArrayHashMap(Formula, void, Formula.ArrayMapContext, false),

        pub fn init(alloc: std.mem.Allocator) FormulaSet {
            return FormulaSet{
                .items = std.ArrayHashMap(Formula, void, Formula.ArrayMapContext, false).init(alloc),
            };
        }

        pub fn contains(self: @This(), it: Formula) bool {
            if (it == .top) return true;
            if (it == .bot) return false;
            return self.items.contains(it);
        }

        pub fn put(self: *@This(), it: Formula, val: void) !void {
            try self.items.put(it, val);
        }

        pub fn putAssumeCapacity(self: *@This(), it: Formula, val: void) void {
            self.items.putAssumeCapacity(it, val);
        }

        pub fn keys(self: @This()) []const Formula {
            return self.items.keys();
        }

        pub fn count(self: @This()) usize {
            return self.items.count();
        }

        pub fn deinit(self: *@This()) void {
            self.items.deinit();
        }

        pub fn ensureTotalCapacity(self: *@This(), new_capacity: usize) !void {
            try self.items.ensureTotalCapacity(new_capacity);
        }

        pub fn clone(self: @This()) !FormulaSet {
            return FormulaSet{
                .items = try self.items.clone(),
            };
        }

        pub fn remove(self: *@This(), key: Formula) void {
            self.items.swapRemove(key);
        }
    };

    set: FormulaSet,
    closure: []const Formula,

    pub const ArraySetContext = struct {
        pub fn hash(_: @This(), atom: Atom) u32 {
            var sum: u32 = 0;
            const formula_ctx = Formula.ArrayMapContext{};
            for (atom.set.keys()) |k| {
                sum |= formula_ctx.hash(k);
            }
            return sum;
        }

        pub fn eql(_: @This(), left: Atom, right: Atom, _: usize) bool {
            return left.set.count() == right.set.count() and blk: {
                for (left.set.keys()) |k| {
                    if (!right.set.contains(k)) break :blk false;
                }
                break :blk true;
            };
        }
    };

    pub fn deinit(self: *@This()) void {
        self.set.deinit();
    }

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        try writer.print("{{ ", .{});
        atom_loop: for (self.set.keys(), 0..) |k, i| {
            switch (k) {
                .lnot => |n| {
                    switch (n.neg) {
                        .trans => continue :atom_loop,
                        else => {},
                    }
                },
                else => {},
            }
            try writer.print("{}", .{k});
            if (i < self.set.count() - 1) {
                try writer.print(", ", .{});
            }
        }
        try writer.print(" }}", .{});
    }

    pub fn glNext(self: @This(), other: @This()) bool {
        for (self.closure) |f| {
            switch (f) {
                .xg => |n| {
                    if (self.set.contains(f) != other.set.contains(n.next)) return false;
                },
                else => {},
            }
        }
        return true;
    }

    pub fn absNext(self: @This(), other: @This()) bool {
        for (self.closure) |f| {
            switch (f) {
                .xa => |n| {
                    if (self.set.contains(f) != other.set.contains(n.next)) return false;
                },
                else => {},
            }
        }
        return true;
    }

    pub fn calNext(self: @This(), other: @This()) bool {
        for (self.closure) |f| {
            switch (f) {
                .xc => |n| {
                    if (self.set.contains(f) != other.set.contains(n.next)) return false;
                },
                else => {},
            }
        }
        return true;
    }

    pub fn containsAPsExactly(self: @This(), aps: std.StringArrayHashMap(void)) bool {
        var ap_count: usize = 0;
        for (self.set.keys()) |f| {
            switch (f) {
                .at => |at| {
                    ap_count += 1;
                    if (!aps.contains(at.name)) return false;
                },
                else => {},
            }
        }
        return ap_count == aps.count();
    }

    pub fn isTransition(self: @This(), trans: Formula.TransLabel) bool {
        for (self.set.keys()) |f| {
            switch (f) {
                .trans => |t| {
                    return t == trans;
                },
                else => {},
            }
        }
        unreachable; // this is not an atom!
    }

    pub fn absFormsEmpty(self: @This()) bool {
        for (self.set.keys()) |f| {
            switch (f) {
                .xa => return false,
                else => {},
            }
        }
        return true;
    }

    pub fn calFormsEmpty(self: @This()) bool {
        for (self.set.keys()) |f| {
            switch (f) {
                .xc => return false,
                else => {},
            }
        }
        return true;
    }

    pub fn calFormsEqual(self: @This(), other: Atom) bool {
        for (self.closure) |f| {
            switch (f) {
                .xc => {
                    if (self.set.contains(f) != other.set.contains(f)) return false;
                },
                else => {},
            }
        }
        return true;
    }

    fn mustHave(f: *const Formula, set: *const FormulaSet) bool {
        switch (f.*) {
            .lnot => |n| {
                if (!set.contains(n.neg)) return true;
            },
            .lor => |n| {
                if (set.contains(n.left) or set.contains(n.right)) return true;
            },
            .ug => |n| {
                if (set.contains(n.right)) return true;
            },
            .ua => |n| {
                if (set.contains(n.right)) return true;
            },
            .uc => |n| {
                if (set.contains(n.right)) return true;
            },
            .xg => |xn| {
                if (xn.next == .ug) {
                    const n = xn.next.ug;
                    if (set.contains(xn.next) and !set.contains(n.right)) return true;
                }
            },
            .xa => |xn| {
                if (xn.next == .ua) {
                    const n = xn.next.ua;
                    if (set.contains(xn.next) and !set.contains(n.right)) return true;
                }
            },
            .xc => |xn| {
                if (xn.next == .uc) {
                    const n = xn.next.uc;
                    if (set.contains(xn.next) and !set.contains(n.right)) return true;
                }
            },
            else => {},
        }
        return false;
    }

    fn conflicts(f: *const Formula, set: *const FormulaSet) bool {
        switch (f.*) {
            .trans => |t| {
                const labels: []const Formula.TransLabel = &.{ .call, .int, .ret };
                for (labels) |l| {
                    if (t != l and set.contains(Formula{ .trans = l })) return true;
                }
            },
            .lnot => |n| {
                if (set.contains(n.neg)) return true;
            },
            .lor => |n| {
                if (!set.contains(n.left) and !set.contains(n.right)) return true;
            },
            .xg => |xn| {
                if (xn.next == .ug) {
                    const n = xn.next.ug;
                    if (!set.contains(xn.next) and set.contains(n.left)) return true;
                }
            },
            .xa => |xn| {
                if (xn.next == .ua) {
                    const n = xn.next.ua;
                    if (!set.contains(xn.next) and set.contains(n.left)) return true;
                }
            },
            .xc => |xn| {
                if (xn.next == .uc) {
                    const n = xn.next.uc;
                    if (!set.contains(xn.next) and set.contains(n.left)) return true;
                }
            },
            else => {},
        }
        switch (f.*) {
            .lnot => {},
            else => {
                const n = Formula{ .lnot = &.{ .neg = f.* } };
                if (set.contains(n)) return true;
            },
        }
        return false;
    }

    fn getSubsetsAux(
        closure: []const Formula,
        i: usize,
        res: *std.ArrayList(FormulaSet),
        subset: *FormulaSet,
    ) !void {
        if (i == closure.len) {
            try res.append(try subset.clone());
            return;
        }
        if (!conflicts(&closure[i], subset)) {
            try subset.put(closure[i], {});
            try getSubsetsAux(closure, i + 1, res, subset);
            _ = subset.items.swapRemove(closure[i]);
        }
        if (!mustHave(&closure[i], subset)) {
            try getSubsetsAux(closure, i + 1, res, subset);
        }
    }

    pub fn getClosureSubsets(gpa: std.mem.Allocator, closure: []const Formula) !std.ArrayList(FormulaSet) {
        var res = std.ArrayList(FormulaSet).init(gpa);
        var subset = FormulaSet.init(gpa);
        defer subset.deinit();
        try getSubsetsAux(closure, 0, &res, &subset);
        return res;
    }

    pub fn getAtoms(gpa: std.mem.Allocator, closure: []const Formula) ![]Atom {
        var visited = std.ArrayHashMap(Atom, void, Atom.ArraySetContext, false).init(gpa);
        defer {
            visited.deinit();
        }
        std.debug.print("", .{});
        var subsets: std.ArrayList(FormulaSet) = try getClosureSubsets(gpa, closure);
        defer {
            for (subsets.items) |*set| {
                set.deinit();
            }
            subsets.deinit();
        }

        for (subsets.items) |set| {
            if (isAtom(set, closure)) {
                var atom = Atom{ .set = set, .closure = closure };
                if (visited.contains(atom)) continue;
                // std.debug.print("{}\n", .{atom});
                atom.set = try set.clone();
                try visited.put(atom, {});
            }
        }
        const res = try gpa.dupe(Atom, visited.keys());
        return res;
    }

    pub fn isAtom(set: FormulaSet, closure: []const Formula) bool {
        var trans_count: u32 = 0;
        for (closure) |f| {
            switch (f) {
                .lnot => |n| {
                    if (set.contains(n.neg) == set.contains(f)) return false;
                },
                else => {
                    const neg = processor.Caret.Formula{ .lnot = &processor.Caret.Lnot{ .neg = f } };
                    if (set.contains(neg) == set.contains(f)) return false;
                },
            }
            switch (f) {
                .lor => |n| {
                    if (set.contains(f) != (set.contains(n.left) or set.contains(n.right))) return false;
                },
                .ug => |n| {
                    if (set.contains(f) != ((set.contains(n.left) and set.contains(processor.Caret.Formula{ .xg = &processor.Caret.Xg{ .next = f } })) or set.contains(n.right))) return false;
                },
                .ua => |n| {
                    if (set.contains(f) != ((set.contains(n.left) and set.contains(processor.Caret.Formula{ .xa = &processor.Caret.Xa{ .next = f } })) or set.contains(n.right))) return false;
                },
                .uc => |n| {
                    if (set.contains(f) != ((set.contains(n.left) and set.contains(processor.Caret.Formula{ .xc = &processor.Caret.Xc{ .next = f } })) or set.contains(n.right))) return false;
                },
                else => {},
            }
            if (f == .trans and set.contains(f)) {
                trans_count += 1;
            }
        }
        if (trans_count != 1) return false;
        return true;
    }
};

pub const ExitLabel = enum(u2) { exit, unexit };

pub const State = packed struct {
    control_point: processor.State,
    atom: AtomName,
    label: ExitLabel,
};

pub const RetSymbol = packed struct {
    symbol: processor.Symbol,
    atom: AtomName,
    label: ExitLabel,
};

pub const Symbol = union(enum) {
    standard: processor.Symbol,
    ret: RetSymbol,
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

pub const AtomName = *const Atom;
pub const StateName = *const State;
pub const SymbolName = *const Symbol;
pub const PhaseName = processor.PhaseName;

pub const PhasePrinter = struct {
    printer: SM_GBPDS_Printer,
    phase: processor.PhaseName,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        const keys = self.printer.proc.phase_names.phase_values.get(self.phase).?.items.keys();
        for (keys, 0..) |r, i| {
            try writer.print("{s}", .{self.printer.rule_names.get(r).?});
            if (i < keys.len - 1) try writer.print(", ", .{});
        }
    }
};

pub const StatePrinter = struct {
    printer: SM_GBPDS_Printer,
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
        try writer.print("<{s}, {}, {s}>", .{
            self.printer.state_names.get(self.state.control_point).?,
            self.state.atom.*,
            switch (self.state.label) {
                .exit => "e",
                .unexit => "u",
            },
        });
    }
};

pub const RulePrinter = struct {
    printer: SM_GBPDS_Printer,
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
                        self.printer.rule_names.get(rule.label).?,
                        self.printer.state(rule.from.*),
                        self.printer.symbol(rule.top.*),
                        self.printer.state(rule.to.*),
                        self.printer.symbol(rule.new_top.?.*),
                        self.printer.symbol(rule.new_tail.?.*),
                    });
                } else if (rule.new_top != null) {
                    try writer.print("{s}: {} {} -> {} {}", .{
                        self.printer.rule_names.get(rule.label).?,
                        self.printer.state(rule.from.*),
                        self.printer.symbol(rule.top.*),
                        self.printer.state(rule.to.*),
                        self.printer.symbol(rule.new_top.?.*),
                    });
                } else {
                    try writer.print("{s}: {} {} -> {}", .{
                        self.printer.rule_names.get(rule.label).?,
                        self.printer.state(rule.from.*),
                        self.printer.symbol(rule.top.*),
                        self.printer.state(rule.to.*),
                    });
                }
            },
            .sm => |rule| {
                try writer.print("{s}: {} -({} / {})-> {}", .{
                    self.printer.rule_names.get(rule.label).?,
                    self.printer.state(rule.from.*),
                    self.printer.phase(rule.old_rules),
                    self.printer.phase(rule.new_rules),
                    self.printer.state(rule.to.*),
                });
            },
        }
    }
};

pub const SymbolPrinter = struct {
    printer: SM_GBPDS_Printer,
    symbol: Symbol,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        switch (self.symbol) {
            .standard => |s| {
                try writer.print("{s}", .{self.printer.symbol_names.get(s).?});
            },
            .ret => |s| {
                try writer.print("|{s}, {}, {s}|", .{
                    self.printer.symbol_names.get(s.symbol).?,
                    s.atom.*,
                    switch (s.label) {
                        .exit => "e",
                        .unexit => "u",
                    },
                });
            },
        }
    }
};

pub const SM_GBPDS_Printer = struct {
    proc: *processor.SM_PDS_Processor,
    state_names: std.AutoHashMap(processor.State, []const u8),
    symbol_names: std.AutoHashMap(processor.Symbol, []const u8),
    rule_names: std.AutoHashMap(processor.RuleName, []const u8),

    pub fn init(gpa: std.mem.Allocator, proc: *processor.SM_PDS_Processor) !SM_GBPDS_Printer {
        var state_names = std.AutoHashMap(processor.State, []const u8).init(gpa);
        for (proc.states.state_map.keys()) |name| {
            try state_names.put(proc.states.state_map.get(name).?, name);
        }

        var symbol_names = std.AutoHashMap(processor.Symbol, []const u8).init(gpa);
        for (proc.symbols.symbol_map.keys()) |name| {
            try symbol_names.put(proc.symbols.symbol_map.get(name).?, name);
        }

        var rule_names = std.AutoHashMap(processor.RuleName, []const u8).init(gpa);
        for (proc.rule_names.rule_map.keys()) |name| {
            try rule_names.put(proc.rule_names.rule_map.get(name).?, name);
        }

        return SM_GBPDS_Printer{
            .proc = proc,
            .state_names = state_names,
            .symbol_names = symbol_names,
            .rule_names = rule_names,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.rule_names.deinit();
        self.state_names.deinit();
        self.symbol_names.deinit();
    }

    pub fn rule(self: @This(), r: Rule) RulePrinter {
        return RulePrinter{
            .printer = self,
            .rule = r,
        };
    }

    pub fn symbol(self: @This(), s: Symbol) SymbolPrinter {
        return SymbolPrinter{
            .printer = self,
            .symbol = s,
        };
    }

    pub fn phase(self: @This(), p: PhaseName) PhasePrinter {
        return PhasePrinter{
            .printer = self,
            .phase = p,
        };
    }

    pub fn state(self: @This(), s: State) StatePrinter {
        return StatePrinter{
            .printer = self,
            .state = s,
        };
    }
};

pub const SM_GBPDS_Processor = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    states: std.SinglyLinkedList(State),
    state_names: std.AutoArrayHashMap(State, StateName),

    symbols: std.SinglyLinkedList(Symbol),
    symbol_names: std.AutoArrayHashMap(Symbol, SymbolName),

    rule_set: std.AutoArrayHashMap(Rule, void),
    accept_atoms: []std.AutoArrayHashMap(AtomName, AcceptType),

    sm_pds_proc: ?*const processor.SM_PDS_Processor,

    pub const AcceptType = enum { any, unexit };

    pub fn init(gpa: std.mem.Allocator, arena: std.mem.Allocator) SM_GBPDS_Processor {
        return SM_GBPDS_Processor{
            .arena = arena,
            .gpa = gpa,

            .states = std.SinglyLinkedList(State){},
            .state_names = std.AutoArrayHashMap(State, StateName).init(gpa),

            .symbols = std.SinglyLinkedList(Symbol){},
            .symbol_names = std.AutoArrayHashMap(Symbol, SymbolName).init(gpa),

            .rule_set = std.AutoArrayHashMap(Rule, void).init(gpa),
            .accept_atoms = &.{},

            .sm_pds_proc = null,
        };
    }

    pub fn deinit(self: *@This()) void {
        self.state_names.deinit();
        self.symbol_names.deinit();
        for (self.accept_atoms) |*l| {
            l.deinit();
        }
        self.rule_set.deinit();
        self.gpa.free(self.accept_atoms);
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

    pub fn getSymbolName(self: *@This(), symbol: Symbol) !SymbolName {
        const gop = try self.symbol_names.getOrPut(symbol);
        if (gop.found_existing) {
            return gop.value_ptr.*;
        } else {
            const node = try self.arena.create(std.SinglyLinkedList(Symbol).Node);
            node.* = .{ .data = symbol };
            self.symbols.prepend(node);
            gop.value_ptr.* = &node.data;
            return &node.data;
        }
    }

    pub fn storeRule(self: *@This(), rule: Rule) !void {
        if (self.rule_set.contains(rule)) return;
        try self.rule_set.put(rule, {});
    }

    pub fn constructCallRule(
        self: *@This(),
        r: processor.CallRule,
        r_name: processor.RuleName,
        a_left: AtomName,
        a_right: AtomName,
        l_left: ExitLabel,
        l_right: ExitLabel,
        lambda: processor.LabellingFunction,
    ) !?StandardRule {
        if (!a_left.isTransition(.call)) return null;

        const s_left = r.from;
        const aps_left = lambda.getAPs(s_left);
        if (!a_left.containsAPsExactly(aps_left)) return null;

        const s_right = r.to;
        const aps_right = lambda.getAPs(s_right);
        if (!a_right.containsAPsExactly(aps_right)) return null;

        if (!a_left.glNext(a_right.*)) return null;
        if (!a_right.calNext(a_left.*)) return null;

        if (l_right == .unexit and (l_left != .unexit or !a_left.absFormsEmpty())) return null;

        const new_from = try self.getStateName(State{
            .control_point = s_left,
            .atom = a_left,
            .label = l_left,
        });

        const new_to = try self.getStateName(State{
            .control_point = s_right,
            .atom = a_right,
            .label = l_right,
        });

        const new_new_tail = try self.getSymbolName(Symbol{ .ret = RetSymbol{
            .symbol = r.new_tail,
            .atom = a_left,
            .label = l_left,
        } });

        return StandardRule{
            .label = r_name,
            .from = new_from,
            .to = new_to,
            .top = try self.getSymbolName(Symbol{ .standard = r.top }),
            .new_top = try self.getSymbolName(Symbol{ .standard = r.new_top }),
            .new_tail = new_new_tail,
        };
    }

    pub fn constructRetRulePop(
        self: *@This(),
        r: processor.RetRule,
        r_name: processor.RuleName,
        a_left: AtomName,
        a_right: AtomName,
        l_right: ExitLabel,
        lambda: processor.LabellingFunction,
    ) !?StandardRule {
        if (!a_left.isTransition(.ret)) return null;

        const s_left = r.from;
        const aps_left = lambda.getAPs(s_left);
        if (!a_left.containsAPsExactly(aps_left)) return null;

        const s_right = r.to;
        const aps_right = lambda.getAPs(s_right);
        if (!a_right.containsAPsExactly(aps_right)) return null;

        if (!a_left.glNext(a_right.*)) return null;

        if (!a_left.absFormsEmpty()) return null;

        const new_from = try self.getStateName(State{
            .control_point = s_left,
            .atom = a_left,
            .label = .exit,
        });

        const new_to = try self.getStateName(State{
            .control_point = s_right,
            .atom = a_right,
            .label = l_right,
        });

        return StandardRule{
            .label = r_name,
            .from = new_from,
            .to = new_to,
            .top = try self.getSymbolName(Symbol{ .standard = r.top }),
            .new_top = null,
            .new_tail = null,
        };
    }

    pub fn constructRetRuleDecode(
        self: *@This(),
        r: processor.RetRule,
        r_name: processor.RuleName,
        gamma: processor.Symbol,
        a_left: AtomName,
        a_ret: AtomName,
        l_left: ExitLabel,
        l_ret: ExitLabel,
        lambda: processor.LabellingFunction,
    ) !?StandardRule {
        if (!a_ret.isTransition(.call)) return null;

        const s_left = r.to;
        const aps_left = lambda.getAPs(s_left);
        if (!a_left.containsAPsExactly(aps_left)) return null;

        if (!a_ret.absNext(a_left.*)) return null;
        if (!a_ret.calFormsEqual(a_left.*)) return null;
        if (l_left != l_ret) return null;

        const new_from = try self.getStateName(State{
            .control_point = s_left,
            .atom = a_left,
            .label = l_left,
        });

        const new_to = try self.getStateName(State{
            .control_point = s_left,
            .atom = a_left,
            .label = l_ret,
        });

        const top = try self.getSymbolName(Symbol{ .ret = RetSymbol{
            .symbol = gamma,
            .atom = a_ret,
            .label = l_ret,
        } });

        return StandardRule{
            .label = r_name,
            .from = new_from,
            .to = new_to,
            .top = top,
            .new_top = try self.getSymbolName(Symbol{ .standard = gamma }),
            .new_tail = null,
        };
    }

    pub fn constructIntRule(
        self: *@This(),
        r: processor.InternalRule,
        r_name: processor.RuleName,
        a_left: AtomName,
        a_right: AtomName,
        l_left: ExitLabel,
        lambda: processor.LabellingFunction,
    ) !?StandardRule {
        if (!a_left.isTransition(.int)) return null;

        const s_left = r.from;
        const aps_left = lambda.getAPs(s_left);
        if (!a_left.containsAPsExactly(aps_left)) return null;

        const s_right = r.to;
        const aps_right = lambda.getAPs(s_right);
        if (!a_right.containsAPsExactly(aps_right)) return null;

        if (!a_left.glNext(a_right.*)) return null;
        if (!a_left.absNext(a_right.*)) return null;
        if (!a_left.calFormsEqual(a_right.*)) return null;

        const new_from = try self.getStateName(State{
            .control_point = s_left,
            .atom = a_left,
            .label = l_left,
        });

        const new_to = try self.getStateName(State{
            .control_point = s_right,
            .atom = a_right,
            .label = l_left,
        });

        return StandardRule{
            .label = r_name,
            .from = new_from,
            .to = new_to,
            .top = try self.getSymbolName(Symbol{ .standard = r.top }),
            .new_top = if (r.new_top) |t| try self.getSymbolName(Symbol{ .standard = t }) else null,
            .new_tail = if (r.new_tail) |t| try self.getSymbolName(Symbol{ .standard = t }) else null,
        };
    }

    pub fn constructSMRule(
        self: *@This(),
        r: processor.SMRule,
        r_name: processor.RuleName,
        a_left: AtomName,
        a_right: AtomName,
        l_left: ExitLabel,
        lambda: processor.LabellingFunction,
    ) !?SMRule {
        if (!a_right.isTransition(.int)) return null;

        const s_left = r.from;
        const aps_left = lambda.getAPs(s_left);
        if (!a_left.containsAPsExactly(aps_left)) return null;

        const s_right = r.to;
        const aps_right = lambda.getAPs(s_right);
        if (!a_right.containsAPsExactly(aps_right)) return null;

        if (!a_left.glNext(a_right.*)) return null;
        if (!a_left.absNext(a_right.*)) return null;
        if (!a_left.calFormsEqual(a_right.*)) return null;

        const new_from = try self.getStateName(State{
            .control_point = s_left,
            .atom = a_left,
            .label = l_left,
        });

        const new_to = try self.getStateName(State{
            .control_point = s_right,
            .atom = a_right,
            .label = l_left,
        });

        return SMRule{
            .label = r_name,
            .from = new_from,
            .to = new_to,
            .old_rules = r.old_phase,
            .new_rules = r.new_phase,
        };
    }

    pub fn constructAcceptAtoms(self: @This(), atoms: []const Atom) ![]std.AutoArrayHashMap(AtomName, AcceptType) {
        const gpa = self.gpa;
        var u_ops = std.ArrayList(Formula).init(gpa);
        defer u_ops.deinit();
        if (atoms.len == 0) {
            std.log.err("Invalid closure and atoms!", .{});
            return error.OtherError;
        }
        for (atoms[0].closure) |f| {
            switch (f) {
                .ug, .ua => {
                    try u_ops.append(f);
                },
                else => {},
            }
        }
        const accept_atoms = try gpa.alloc(std.AutoArrayHashMap(AtomName, AcceptType), u_ops.items.len);
        for (u_ops.items, 0..) |op, i| {
            accept_atoms[i] = std.AutoArrayHashMap(AtomName, AcceptType).init(gpa);
            const right_op = switch (op) {
                .ug => |n| n.right,
                .ua => |n| n.right,
                else => unreachable,
            };
            const acc_type = switch (op) {
                .ug => AcceptType.any,
                .ua => AcceptType.unexit,
                else => unreachable,
            };
            for (atoms) |*a| {
                if (!a.set.contains(op) or a.set.contains(right_op)) {
                    try accept_atoms[i].put(a, acc_type);
                }
            }
        }
        return accept_atoms;
    }

    pub fn construct(
        self: *@This(),
        sm_pds_proc: *const processor.SM_PDS_Processor,
        atoms: []const Atom,
        lambda: processor.LabellingFunction,
    ) !void {
        const sm_pds = sm_pds_proc.system.?;
        const label_arr: []const ExitLabel = &.{ ExitLabel.exit, ExitLabel.unexit };

        self.sm_pds_proc = sm_pds_proc;

        self.accept_atoms = try self.constructAcceptAtoms(atoms);

        for (sm_pds.rules.keys()) |r_name| {
            const rule = sm_pds.rules.get(r_name).?;
            switch (rule) {
                .call => |r| {
                    for (atoms) |*a_left| {
                        for (atoms) |*a_right| {
                            for (label_arr) |l_left| {
                                for (label_arr) |l_right| {
                                    const new_r_opt = try self.constructCallRule(
                                        r,
                                        r_name,
                                        a_left,
                                        a_right,
                                        l_left,
                                        l_right,
                                        lambda,
                                    );
                                    if (new_r_opt) |new_r| {
                                        try self.storeRule(Rule{ .standard = new_r });
                                    }
                                }
                            }
                        }
                    }
                },
                .ret => |r| {
                    for (atoms) |*a_left| {
                        for (atoms) |*a_right| {
                            for (label_arr) |l_right| {
                                const new_r_opt = try self.constructRetRulePop(
                                    r,
                                    r_name,
                                    a_left,
                                    a_right,
                                    l_right,
                                    lambda,
                                );
                                if (new_r_opt) |new_r| {
                                    try self.storeRule(Rule{ .standard = new_r });
                                }

                                for (sm_pds.alphabet) |gamma| {
                                    const new_r_decode_opt = try self.constructRetRuleDecode(
                                        r,
                                        r_name,
                                        gamma,
                                        a_left,
                                        a_right,
                                        l_right,
                                        l_right,
                                        lambda,
                                    );
                                    if (new_r_decode_opt) |new_r| {
                                        try self.storeRule(Rule{ .standard = new_r });
                                    }
                                }
                            }
                        }
                    }
                },
                .int => |r| {
                    for (atoms) |*a_left| {
                        for (atoms) |*a_right| {
                            for (label_arr) |l_left| {
                                const new_r_opt = try self.constructIntRule(
                                    r,
                                    r_name,
                                    a_left,
                                    a_right,
                                    l_left,
                                    lambda,
                                );
                                if (new_r_opt) |new_r| {
                                    try self.storeRule(Rule{ .standard = new_r });
                                }
                            }
                        }
                    }
                },
                .sm => |r| {
                    for (atoms) |*a_left| {
                        for (atoms) |*a_right| {
                            for (label_arr) |l_left| {
                                const new_r_opt = try self.constructSMRule(
                                    r,
                                    r_name,
                                    a_left,
                                    a_right,
                                    l_left,
                                    lambda,
                                );
                                if (new_r_opt) |new_r| {
                                    try self.storeRule(Rule{ .sm = new_r });
                                }
                            }
                        }
                    }
                },
            }
        }
    }

    pub fn simplify(self: *@This(), inits: []const StateName) !void {
        var arena = std.heap.ArenaAllocator.init(self.arena);
        defer arena.deinit();

        var i: usize = 0;

        while (try self.simplifyStep(arena.allocator(), inits) > 0) : (_ = arena.reset(.retain_capacity)) {
            i += 1;
            // std.debug.print("Simplify {}:\n", .{i});
        }
    }

    fn simplifyStep(self: *@This(), arena: std.mem.Allocator, inits: []const StateName) !u32 {
        // var timer = try std.time.Timer.start();
        var deleted: u32 = 0;

        var ret_sym_pushed = std.AutoHashMap(RetSymbol, void).init(arena);
        defer ret_sym_pushed.deinit();
        var ret_sym_read = std.AutoHashMap(RetSymbol, void).init(arena);
        defer ret_sym_read.deinit();

        for (self.rule_set.keys()) |rule| {
            switch (rule) {
                .standard => |r| {
                    if (r.new_tail) |tail| {
                        switch (tail.*) {
                            .ret => |top| {
                                try ret_sym_pushed.put(top, {});
                            },
                            .standard => {},
                        }
                    }
                    switch (r.top.*) {
                        .ret => |top| {
                            try ret_sym_read.put(top, {});
                        },
                        .standard => {},
                    }
                },
                .sm => {},
            }
        }

        // std.debug.print("Ret Sym scan: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});

        var srcs_used = std.AutoHashMap(StateName, void).init(arena);
        defer srcs_used.deinit();

        var trg_used = std.AutoHashMap(StateName, void).init(arena);
        defer trg_used.deinit();

        for (inits) |i| {
            try trg_used.put(i, {});
        }

        for (self.rule_set.keys()) |rule| {
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
        // std.debug.print("State scan: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});

        var to_del = std.ArrayList(Rule).init(arena);
        defer to_del.deinit();

        for (self.rule_set.keys()) |rule| {
            switch (rule) {
                .standard => |r| {
                    if (!srcs_used.contains(r.to) or !trg_used.contains(r.from)) {
                        try to_del.append(rule);
                    } else {
                        switch (r.top.*) {
                            .ret => |t| {
                                if (!ret_sym_pushed.contains(t)) {
                                    try to_del.append(rule);
                                }
                            },
                            .standard => {},
                        }
                        // if (r.new_tail) |tail| {
                        //     switch (tail.*) {
                        //         .ret => |top| {
                        //             if (!ret_sym_read.contains(top)) {
                        //                 try to_del.append(rule);
                        //             }
                        //         },
                        //         .standard => {},
                        //     }
                        // }
                    }
                },
                .sm => |r| {
                    if (!srcs_used.contains(r.to) or !trg_used.contains(r.from)) {
                        try to_del.append(rule);
                    }
                },
            }
        }
        // std.debug.print("Rule scan: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});

        for (to_del.items) |r| {
            if (self.rule_set.swapRemove(r)) {
                deleted += 1;
            }
        }
        // std.debug.print("Deletion: {d:.3}s\n", .{@as(f64, @floatFromInt(timer.lap())) / 1000000000});
        return deleted;
    }
};

test "isAtom" {
    const Caret = processor.Caret;
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
    const closure = try formula.get_closure(alloc);
    defer {
        for (closure) |f| {
            f.deinit(alloc);
        }
        alloc.free(closure);
    }

    var at = Atom.FormulaSet.init(alloc);
    defer at.deinit();
    try at.put(Caret.Formula{
        .at = &Caret.At{ .name = "123" },
    }, {});
    try at.put(Caret.Formula{
        .xa = &Caret.Xa{
            .next = Caret.Formula{
                .at = &Caret.At{ .name = "123" },
            },
        },
    }, {});
    try at.put(Caret.Formula{
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
    }, {});

    try at.put(Caret.Formula{ .xg = &Caret.Xg{
        .next = Caret.Formula{
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
        },
    } }, {});
    try at.put(Caret.Formula{
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
    }, {});
    try at.put(Caret.Formula{ .trans = .call }, {});
    try at.put(Caret.Formula{ .lnot = &Caret.Lnot{ .neg = Caret.Formula{ .trans = .int } } }, {});
    try at.put(Caret.Formula{ .lnot = &Caret.Lnot{ .neg = Caret.Formula{ .trans = .ret } } }, {});

    try std.testing.expect(Atom.isAtom(at, closure));
}

test "atoms12" {
    const alloc = std.testing.allocator;
    const Caret = processor.Caret;

    const formula = Caret.Formula{
        .ug = &Caret.Ug{
            .left = Caret.Formula{ .top = {} },
            .right = Caret.Formula{ .at = &Caret.At{ .name = "456" } },
        },
    };

    const closure: []const Caret.Formula = try formula.get_closure(alloc);
    defer {
        for (closure) |f| {
            f.deinit(alloc);
        }
        alloc.free(closure);
    }
    const atoms = try Atom.getAtoms(alloc, closure);
    defer {
        for (atoms) |*a| {
            a.deinit();
        }
        alloc.free(atoms);
    }

    // for (atoms) |a| {
    //     std.debug.print("{}\n", .{a});
    // }

    try std.testing.expectEqual(12, atoms.len);
}

test "atoms48" {
    const alloc = std.testing.allocator;
    const Caret = processor.Caret;

    const formula = Caret.Formula{
        .ug = &Caret.Ug{
            .left = Caret.Formula{ .top = {} },
            .right = Caret.Formula{
                .lnot = &.{ .neg = Caret.Formula{
                    .lor = &.{
                        .left = Caret.Formula{
                            .lnot = &Caret.Lnot{
                                .neg = Caret.Formula{ .at = &Caret.At{ .name = "123" } },
                            },
                        },
                        .right = Caret.Formula{
                            .lnot = &.{ .neg = Caret.Formula{
                                .ug = &.{
                                    .left = Caret.Formula{ .top = {} },
                                    .right = Caret.Formula{ .at = &Caret.At{ .name = "456" } },
                                },
                            } },
                        },
                    },
                } },
            },
        },
    };

    const closure: []const Caret.Formula = try formula.get_closure(alloc);
    defer {
        for (closure) |f| {
            f.deinit(alloc);
        }
        alloc.free(closure);
    }
    const atoms = try Atom.getAtoms(alloc, closure);
    defer {
        for (atoms) |*a| {
            a.deinit();
        }
        alloc.free(atoms);
    }

    try std.testing.expectEqual(48, atoms.len);
}

const parser = @import("parser.zig");

test "sm-gbpds construction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var proc = processor.SM_PDS_Processor.init(allocator, std.testing.allocator);
    defer proc.deinit();

    var file = parser.SmpdsFile.open(allocator, "examples/process_test.smpds");

    const unprocessed_conf = try file.parse();
    const unprocessed = unprocessed_conf.smpds;
    try proc.process(unprocessed, unprocessed_conf.init);
    _ = try proc.getInit(unprocessed_conf.init);

    var gbpds = SM_GBPDS_Processor.init(std.testing.allocator, allocator);
    defer gbpds.deinit();

    const formula = try processor.processCaret(allocator, unprocessed_conf.caret);

    const closure = try formula.get_closure(std.testing.allocator);
    defer {
        for (closure) |f| {
            f.deinit(std.testing.allocator);
        }
        std.testing.allocator.free(closure);
    }

    const atoms = try Atom.getAtoms(std.testing.allocator, closure);
    defer {
        for (atoms) |*a| {
            a.deinit();
        }
        std.testing.allocator.free(atoms);
    }

    var lambda = try processor.LabellingFunction.init(std.testing.allocator, &proc, formula, processor.LabellingFunction.strict);
    defer lambda.deinit();

    try gbpds.construct(&proc, atoms, lambda);

    var printer = try SM_GBPDS_Printer.init(std.testing.allocator, &proc);
    defer printer.deinit();

    try std.testing.expectEqual(2, gbpds.accept_atoms.len);

    // for (gbpds.accept_atoms, 0..) |l, i| {
    //     std.debug.print("{}:\n", .{i});
    //     for (l.keys()) |a| {
    //         std.debug.print("\t{}\n", .{a.*});
    //     }
    // }

    // var it = gbpds.rules.first;
    // while (it) |node| : (it = node.next) {
    //     std.debug.print("{}\n", .{printer.rule(node.data)});
    // }
}

// This is a nice idea to precompile formula like SPIN, but it is impossible
// because comptime allocations don't work

// test "comptime closure" {
//     comptime {
//         var buf: [1000000]u8 = undefined;
//         var fba = std.heap.FixedBufferAllocator.init(&buf);
//         const alloc = fba.allocator();

//         const Caret = processor.Caret;
//         const formula = Caret.Formula{
//             .ug = &Caret.Ug{
//                 .left = Caret.Formula{ .top = {} },
//                 .right = Caret.Formula{
//                     .at = &Caret.At{ .name = "123" },
//                 },
//             },
//         };

//         const closure: []const Caret.Formula = try formula.get_closure(alloc);
//         _ = closure;
//     }
// }
