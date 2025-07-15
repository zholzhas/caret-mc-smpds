const buchi = @import("sm_bpds.zig");
const std = @import("std");

pub const Head = struct {
    state: buchi.StateName,
    phase: buchi.PhaseName,
    top: buchi.SymbolName,

    index: ?u32 = null,
    lowlink: ?u32 = null,
    on_stack: ?bool = null,
};

pub const Edge = struct {
    from: *const Head,
    label: bool,
    to: *const Head,
};

pub const HeadState = struct {
    state: buchi.StateName,
    phase: buchi.PhaseName,
};

pub const HeadReachabilityGraph = struct {
    arena: std.mem.Allocator,
    gpa: std.mem.Allocator,

    pre_ma: *const buchi.MA,
    sm_bpds: *const buchi.SM_BPDS_Processor,

    heads: std.AutoArrayHashMap(Head, *Head),

    edges: std.AutoArrayHashMap(Edge, *const Edge),
    edges_by_src: std.AutoHashMap(*const Head, std.SinglyLinkedList(*const Edge)),

    heads_by_state: std.AutoHashMap(HeadState, std.SinglyLinkedList(*const Head)),

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator, pre_ma: *const buchi.MA, sm_bpds: *const buchi.SM_BPDS_Processor) @This() {
        return @This(){
            .arena = arena,
            .gpa = gpa,

            .pre_ma = pre_ma,
            .sm_bpds = sm_bpds,

            .edges = std.AutoArrayHashMap(Edge, *const Edge).init(gpa),
            .edges_by_src = std.AutoHashMap(*const Head, std.SinglyLinkedList(*const Edge)).init(gpa),

            .heads_by_state = std.AutoHashMap(HeadState, std.SinglyLinkedList(*const Head)).init(gpa),
            .heads = std.AutoArrayHashMap(Head, *Head).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.edges.deinit();
        self.edges_by_src.deinit();
        self.heads_by_state.deinit();
        self.heads.deinit();
    }

    pub const HRErr = error{
        AddingEdgeAfterTarjan,
    };

    fn addHead(self: *@This(), head: Head) !*const Head {
        if (head.index != null) {
            std.log.err("Cannot add edges after searching repeating heads!", .{});
            return HRErr.AddingEdgeAfterTarjan;
        }
        if (self.heads.get(head)) |h_ptr| {
            return h_ptr;
        }
        const head_ptr = try self.arena.create(Head);
        head_ptr.* = head;
        try self.heads.put(head, head_ptr);
        return head_ptr;
    }

    fn addEdge(self: *@This(), edge: Edge) !bool {
        if (self.edges.contains(edge)) {
            return false;
        }

        const src = edge.from;
        const edge_ptr = try self.arena.create(Edge);
        edge_ptr.* = edge;

        try self.edges.put(edge, edge_ptr);

        {
            const gop = try self.edges_by_src.getOrPut(src);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.SinglyLinkedList(*const Edge){};
            }
            const node_ptr = try self.arena.create(std.SinglyLinkedList(*const Edge).Node);
            node_ptr.* = std.SinglyLinkedList(*const Edge).Node{
                .data = edge_ptr,
            };
            gop.value_ptr.prepend(node_ptr);
        }

        {
            const gop = try self.heads_by_state.getOrPut(HeadState{ .state = edge.from.state, .phase = edge.from.phase });
            if (!gop.found_existing) {
                gop.value_ptr.* = std.SinglyLinkedList(*const Head){};
            }
            const node_ptr = try self.arena.create(std.SinglyLinkedList(*const Head).Node);
            node_ptr.* = std.SinglyLinkedList(*const Head).Node{
                .data = edge.from,
            };
            gop.value_ptr.prepend(node_ptr);
        }

        {
            const gop = try self.heads_by_state.getOrPut(HeadState{ .state = edge.to.state, .phase = edge.to.phase });
            if (!gop.found_existing) {
                gop.value_ptr.* = std.SinglyLinkedList(*const Head){};
            }
            const node_ptr = try self.arena.create(std.SinglyLinkedList(*const Head).Node);
            node_ptr.* = std.SinglyLinkedList(*const Head).Node{
                .data = edge.to,
            };
            gop.value_ptr.prepend(node_ptr);
        }

        return true;
    }

    pub fn construct(self: *@This()) !void {
        var path_arena = std.heap.ArenaAllocator.init(self.arena);
        defer path_arena.deinit();

        for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.keys()) |phase_name| {
            const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(phase_name).?;

            rule_loop: for (self.sm_bpds.rules.keys()) |rule| {
                switch (rule) {
                    .sm => {},
                    .standard => |r| {
                        if (!phase.items.contains(r.label)) {
                            continue :rule_loop;
                        }
                        if (r.new_top != null) {
                            _ = try self.addEdge(Edge{
                                .from = try self.addHead(Head{
                                    .state = r.from,
                                    .phase = phase_name,
                                    .top = r.top,
                                }),
                                .label = self.sm_bpds.isAccepting(r.from.*),
                                .to = try self.addHead(Head{
                                    .state = r.to,
                                    .phase = phase_name,
                                    .top = r.new_top.?,
                                }),
                            });
                        }
                        if (r.new_tail != null) {
                            _ = path_arena.reset(.retain_capacity);
                            const paths = try self.pre_ma.hasPath(path_arena.allocator(), buchi.MA.Node{ .st = .{ .state = r.to, .phase = phase_name } }, &.{r.new_top.?});
                            for (paths) |path| {
                                _ = try self.addEdge(Edge{
                                    .from = try self.addHead(Head{
                                        .state = r.from,
                                        .phase = phase_name,
                                        .top = r.top,
                                    }),
                                    .label = self.sm_bpds.isAccepting(r.from.*) or path.accepting,
                                    .to = try self.addHead(Head{
                                        .state = path.end_node.st.state,
                                        .phase = path.end_node.st.phase,
                                        .top = r.new_tail.?,
                                    }),
                                });
                            }
                        }
                    },
                }
            }
        }

        for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.keys()) |phase_name| {
            const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(phase_name).?;
            rule_loop: for (self.sm_bpds.rules.keys()) |rule| {
                switch (rule) {
                    .standard => {},
                    .sm => |r| {
                        if (!phase.items.contains(r.label)) {
                            continue :rule_loop;
                        }
                        const next_phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.get(.{
                            .original_phase = phase_name,
                            .to_add = r.new_rules,
                            .to_remove = r.old_rules,
                        }) orelse continue :rule_loop; // continue because it means for rule p -(r1 / r2)-> p1 there is no r1 in phase.

                        from_heads: {
                            const head_list = (self.heads_by_state.get(HeadState{ .state = r.from, .phase = phase_name }) orelse break :from_heads);
                            var head_it = head_list.first;
                            while (head_it) |head_node| : (head_it = head_node.next) {
                                _ = try self.addEdge(Edge{
                                    .from = head_node.data,
                                    .label = self.sm_bpds.isAccepting(r.from.*),
                                    .to = try self.addHead(Head{
                                        .state = r.to,
                                        .phase = next_phase,
                                        .top = head_node.data.top,
                                    }),
                                });
                            }
                        }
                        to_heads: {
                            const head_list = (self.heads_by_state.get(HeadState{ .state = r.to, .phase = next_phase }) orelse break :to_heads);
                            var head_it = head_list.first;
                            while (head_it) |head_node| : (head_it = head_node.next) {
                                _ = try self.addEdge(Edge{
                                    .from = try self.addHead(Head{
                                        .state = r.from,
                                        .phase = phase_name,
                                        .top = head_node.data.top,
                                    }),
                                    .label = self.sm_bpds.isAccepting(r.from.*),
                                    .to = head_node.data,
                                });
                            }
                        }
                    },
                }
            }
        }
    }

    // Strongly connected component
    pub const SCC = struct {
        heads: []const *const Head,
    };

    // Tarjan algo
    pub fn findRepeatingHeads(self: *const @This(), gpa: std.mem.Allocator) ![]SCC {
        var index: u32 = 0;

        var stack = std.ArrayList(*Head).init(gpa);
        defer stack.deinit();

        var sccs = std.ArrayList(SCC).init(gpa);
        defer sccs.deinit();

        for (self.heads.values()) |head| {
            if (head.index == null) {
                try self.strongconnect(gpa, head, &stack, &index, &sccs);
            }
        }

        return try sccs.toOwnedSlice();
    }

    pub var global_printer: ?*Printer = null;

    fn strongconnect(self: *const @This(), gpa: std.mem.Allocator, head: *Head, stack: *std.ArrayList(*Head), index: *u32, sccs: *std.ArrayList(SCC)) !void {
        head.*.index = index.*;
        head.*.lowlink = index.*;
        index.* += 1;
        try stack.append(head);
        head.*.on_stack = true;

        const edges = self.edges_by_src.get(head);
        if (edges) |edge_list| {
            var edge_it = edge_list.first;
            while (edge_it) |edge_node| : (edge_it = edge_node.next) {
                const to = edge_node.data.to;
                if (to.*.index == null) {
                    try self.strongconnect(gpa, @constCast(to), stack, index, sccs);
                    head.*.lowlink = @min(head.lowlink.?, to.lowlink.?);
                } else if (to.*.on_stack.?) {
                    head.*.lowlink = @min(head.lowlink.?, to.index.?);
                }
            }
        }

        if (head.*.lowlink.? == head.*.index.?) {
            if (global_printer) |p| {
                std.debug.print("Starting component from {}\n", .{p.node(head.*)});
            }
            var heads = std.ArrayList(*const Head).init(gpa);
            defer heads.deinit();
            while (stack.pop()) |h| {
                h.*.on_stack = false;
                try heads.append(h);

                if (h == head) break;
            }

            var accepting = false;
            is_acc: for (heads.items) |h1| {
                for (heads.items) |h2| {
                    if (self.edges.contains(Edge{
                        .from = h1,
                        .label = true,
                        .to = h2,
                    })) {
                        accepting = true;
                        break :is_acc;
                    }
                }
            }

            if (accepting) {
                const scc = SCC{
                    .heads = try heads.toOwnedSlice(),
                };
                try sccs.append(scc);
            }
        }
    }

    pub const Printer = struct {
        const Parent = @This();
        const Node = Head;

        gen: *buchi.SM_BPDS_Printer,
        pub fn init(gen: *buchi.SM_BPDS_Printer) Printer {
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
                try writer.print("[{}, {}, {}]", .{ self.printer.gen.state(self.node.state.*), self.printer.gen.gen.symbol(self.node.top.*), self.printer.gen.gen.phase(self.node.phase) });
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
                try writer.print("{} -->{s} {}", .{ self.printer.node(self.edge.from.*), if (self.edge.label) ">" else "", self.printer.node(self.edge.to.*) });
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

pub fn build_hr_pre(ma: *buchi.MA, sccs: []const HeadReachabilityGraph.SCC) !void {
    const acc_node = buchi.MA.Node{
        .int = .{ .id = 0, .accepting = true },
    };
    _ = try ma.addEdge(.{
        .from = acc_node,
        .to = acc_node,
        .accepting = false,
        .symbol = .{ .star = {} },
    });

    for (sccs) |scc| {
        for (scc.heads) |head| {
            _ = try ma.addEdge(.{
                .from = .{ .st = .{
                    .state = head.state,
                    .phase = head.phase,
                } },
                .to = acc_node,
                .accepting = false,
                .symbol = .{ .symbol = head.top },
            });
        }
    }
}
