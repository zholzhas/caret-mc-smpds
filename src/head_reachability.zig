const buchi = @import("sm_bpds.zig");
const std = @import("std");
const root = @import("main.zig");

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

    pre_ma: *buchi.MA,
    sm_bpds: *const buchi.SM_BPDS_Processor,

    heads: std.AutoArrayHashMap(Head, *Head),

    edges: std.AutoArrayHashMap(Edge, *const Edge),
    edges_by_src: std.AutoHashMap(*const Head, std.SinglyLinkedList(*const Edge)),
    edges_by_trg: std.AutoHashMap(*const Head, std.SinglyLinkedList(*const Edge)),

    heads_by_state: std.AutoHashMap(HeadState, std.SinglyLinkedList(*const Head)),

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator, pre_ma: *buchi.MA, sm_bpds: *const buchi.SM_BPDS_Processor) @This() {
        return @This(){
            .arena = arena,
            .gpa = gpa,

            .pre_ma = pre_ma,
            .sm_bpds = sm_bpds,

            .edges = std.AutoArrayHashMap(Edge, *const Edge).init(gpa),
            .edges_by_src = std.AutoHashMap(*const Head, std.SinglyLinkedList(*const Edge)).init(gpa),
            .edges_by_trg = std.AutoHashMap(*const Head, std.SinglyLinkedList(*const Edge)).init(gpa),

            .heads_by_state = std.AutoHashMap(HeadState, std.SinglyLinkedList(*const Head)).init(gpa),
            .heads = std.AutoArrayHashMap(Head, *Head).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.edges.deinit();
        self.edges_by_src.deinit();
        self.edges_by_trg.deinit();
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
            const gop = try self.edges_by_trg.getOrPut(edge.to);
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

    pub fn constructSchwoon(self: *@This()) !void {
        //  rel = self.pre_ma

        var trans = std.ArrayList(buchi.MA.Edge).init(self.gpa);
        defer trans.deinit();

        // delta_aux = self.edges

        const RuleTail = struct {
            to: buchi.StateName,
            new_top: ?buchi.SymbolName, // null for self-modifying rules
        };

        var rules_by_tail = std.AutoHashMap(RuleTail, std.ArrayList(*const buchi.Rule)).init(self.gpa);
        defer {
            var it = rules_by_tail.iterator();
            while (it.next()) |e| {
                e.value_ptr.deinit();
            }
            rules_by_tail.deinit();
        }

        for (self.sm_bpds.rules.keys()) |*rule| {
            switch (rule.*) {
                .sm => |r| {
                    const tail = RuleTail{
                        .to = r.to,
                        .new_top = null,
                    };
                    const gop = try rules_by_tail.getOrPut(tail);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = std.ArrayList(*const buchi.Rule).init(self.gpa);
                    }
                    try gop.value_ptr.append(rule);
                },
                .standard => |r| {
                    if (r.new_top == null) continue;
                    const tail = RuleTail{
                        .to = r.to,
                        .new_top = r.new_top.?,
                    };
                    const gop = try rules_by_tail.getOrPut(tail);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = std.ArrayList(*const buchi.Rule).init(self.gpa);
                    }
                    try gop.value_ptr.append(rule);
                },
            }
        }

        if (root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.keys()) |phase_name| {
            const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(phase_name).?;

            rule_loop: for (self.sm_bpds.rules.keys()) |*rule| {
                switch (rule.*) {
                    .sm => {},
                    .standard => |r| {
                        if (!phase.items.contains(r.label)) {
                            continue :rule_loop;
                        }
                        if (r.new_top == null) {
                            try trans.append(buchi.MA.Edge{
                                .from = buchi.MA.Node{
                                    .st = buchi.MA.StateNode{
                                        .state = r.from,
                                        .phase = phase_name,
                                    },
                                },
                                .symbol = buchi.MA.EdgeSymbol{
                                    .symbol = r.top,
                                },
                                .to = buchi.MA.Node{
                                    .st = buchi.MA.StateNode{
                                        .state = r.to,
                                        .phase = phase_name,
                                    },
                                },
                                .accepting = self.sm_bpds.isAccepting(r.from.*),
                            });
                        }
                    },
                }
            }
        }

        if (root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        while (trans.pop()) |edge| {
            if (trans.capacity > trans.items.len * 3) {
                trans.shrinkAndFree(trans.items.len);
            }
            if (self.pre_ma.edge_set.contains(edge)) {
                continue;
            }
            _ = try self.pre_ma.addEdge(edge);

            const hr_edges_opt = self.edges_by_trg.get(try self.addHead(Head{
                .state = edge.from.st.state,
                .phase = edge.from.st.phase,
                .top = edge.symbol.symbol,
            }));
            if (hr_edges_opt) |hr_edges| {
                var cur_hr_edge = hr_edges.first;
                while (cur_hr_edge) |hr_edge| : (cur_hr_edge = hr_edge.next) {
                    try trans.append(buchi.MA.Edge{
                        .from = buchi.MA.Node{
                            .st = buchi.MA.StateNode{
                                .state = hr_edge.data.from.state,
                                .phase = hr_edge.data.from.phase,
                            },
                        },
                        .symbol = buchi.MA.EdgeSymbol{
                            .symbol = hr_edge.data.from.top,
                        },
                        .to = edge.to,
                        .accepting = edge.accepting or hr_edge.data.label,
                    });
                }
            }

            // sm rules
            if (rules_by_tail.get(.{ .to = edge.from.st.state, .new_top = null })) |tail_rules| {
                for (tail_rules.items) |r| {
                    for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.keys()) |prev_phase| {
                        const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(prev_phase).?;
                        if (!phase.items.contains(r.sm.label)) {
                            continue;
                        }
                        const candidate_phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.get(.{
                            .original_phase = prev_phase,
                            .to_remove = r.sm.old_rules,
                            .to_add = r.sm.new_rules,
                        }) orelse {
                            continue;
                            // std.debug.print("Try {}, {}, {}\nIn\n", .{ prev_phase, r.sm.old_rules, r.sm.new_rules });
                            // var it = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.iterator();
                            // while (it.next()) |entr| {
                            //     std.debug.print("<{} -> {}>\n", .{ entr.key_ptr.*, entr.value_ptr.* });
                            // }
                            // unreachable;
                        };
                        if (candidate_phase == edge.from.st.phase) {
                            try trans.append(buchi.MA.Edge{
                                .from = buchi.MA.Node{
                                    .st = buchi.MA.StateNode{
                                        .state = r.sm.from,
                                        .phase = prev_phase,
                                    },
                                },
                                .symbol = edge.symbol,
                                .to = edge.to,
                                .accepting = edge.accepting or self.sm_bpds.isAccepting(r.sm.from.*),
                            });
                        }
                    }
                }
            }

            // standard rules
            if (rules_by_tail.get(.{ .to = edge.from.st.state, .new_top = edge.symbol.symbol })) |tail_rules| {
                const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(edge.from.st.phase).?;

                for (tail_rules.items) |r| {
                    if (!phase.items.contains(r.standard.label)) {
                        continue;
                    }
                    if (r.standard.new_tail == null) {
                        try trans.append(buchi.MA.Edge{
                            .from = buchi.MA.Node{
                                .st = buchi.MA.StateNode{
                                    .state = r.standard.from,
                                    .phase = edge.from.st.phase,
                                },
                            },
                            .symbol = buchi.MA.EdgeSymbol{
                                .symbol = r.standard.top,
                            },
                            .to = edge.to,
                            .accepting = edge.accepting or self.sm_bpds.isAccepting(r.standard.from.*),
                        });
                    } else {
                        _ = try self.addEdge(Edge{
                            .from = try self.addHead(Head{
                                .state = r.standard.from,
                                .phase = edge.from.st.phase,
                                .top = r.standard.top,
                            }),
                            .to = try self.addHead(Head{
                                .state = edge.to.st.state,
                                .phase = edge.to.st.phase,
                                .top = r.standard.new_tail.?,
                            }),
                            .label = edge.accepting or self.sm_bpds.isAccepting(r.standard.from.*),
                        });

                        const aux_edges_opt = self.pre_ma.edges_by_head.get(.{
                            .from = edge.to,
                            .symbol = buchi.MA.EdgeSymbol{ .symbol = r.standard.new_tail.? },
                        });
                        if (aux_edges_opt) |aux_edges| {
                            var edge_it = aux_edges.first;
                            while (edge_it) |edge_aux| : (edge_it = edge_aux.next) {
                                try trans.append(buchi.MA.Edge{
                                    .from = buchi.MA.Node{
                                        .st = buchi.MA.StateNode{
                                            .state = r.standard.from,
                                            .phase = edge.from.st.phase,
                                        },
                                    },
                                    .symbol = buchi.MA.EdgeSymbol{
                                        .symbol = r.standard.top,
                                    },
                                    .to = edge_aux.data.to,
                                    .accepting = edge.accepting or edge_aux.data.accepting or self.sm_bpds.isAccepting(r.standard.from.*),
                                });
                            }
                        }
                    }
                }
            }
        }

        // ------------------------------

        if (root.state_initialized) {
            std.log.info("Adding default hr edges: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }
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
