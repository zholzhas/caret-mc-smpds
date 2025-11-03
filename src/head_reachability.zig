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
    edges_by_src: std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)),
    edges_by_trg: std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)),

    heads_by_state: std.AutoHashMap(HeadState, std.AutoArrayHashMap(*const Head, void)),

    pub fn init(arena: std.mem.Allocator, gpa: std.mem.Allocator, pre_ma: *buchi.MA, sm_bpds: *const buchi.SM_BPDS_Processor) @This() {
        return @This(){
            .arena = arena,
            .gpa = gpa,

            .pre_ma = pre_ma,
            .sm_bpds = sm_bpds,

            .edges = std.AutoArrayHashMap(Edge, *const Edge).init(gpa),
            .edges_by_src = std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)).init(gpa),
            .edges_by_trg = std.AutoHashMap(*const Head, std.AutoArrayHashMap(*const Edge, void)).init(gpa),

            .heads_by_state = std.AutoHashMap(HeadState, std.AutoArrayHashMap(*const Head, void)).init(gpa),
            .heads = std.AutoArrayHashMap(Head, *Head).init(gpa),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.edges.deinit();
        {
            var it = self.edges_by_src.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }

            self.edges_by_src.deinit();
        }
        {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }

            self.edges_by_trg.deinit();
        }
        {
            var it = self.heads_by_state.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }

            self.heads_by_state.deinit();
        }
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
        const edge_ptr = try self.arena.create(Edge);
        edge_ptr.* = edge;

        try self.edges.put(edge, edge_ptr);

        {
            const gop = try self.edges_by_trg.getOrPut(edge.to);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge_ptr, {});
        }

        {
            const gop = try self.heads_by_state.getOrPut(HeadState{ .state = edge.from.state, .phase = edge.from.phase });
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Head, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge.from, {});
        }

        {
            const gop = try self.heads_by_state.getOrPut(HeadState{ .state = edge.to.state, .phase = edge.to.phase });
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Head, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge.to, {});
        }

        return true;
    }

    pub fn constructSchwoon(self: *@This()) !void {
        defer {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }
            self.edges_by_trg.clearAndFree();
        }
        //  rel = self.pre_ma

        var trans = std.SinglyLinkedList(*const buchi.MA.Edge){};
        defer {
            while (trans.popFirst()) |n| {
                self.gpa.destroy(n);
            }
        }
        var trans_set = std.AutoHashMap(*const buchi.MA.Edge, void).init(self.gpa);
        defer trans_set.deinit();

        // delta_aux = self.edges

        const RuleTail = struct {
            to: buchi.StateName,
            new_top: buchi.SymbolName, // null for self-modifying rules
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
                        .new_top = r.top,
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
                            const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
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
                            if (!trans_set.contains(edge_ptr)) {
                                const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                new_node.* = .{ .data = edge_ptr };
                                trans.prepend(new_node);
                                try trans_set.put(edge_ptr, {});
                            }
                        }
                    },
                }
            }
        }

        if (root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        const PrevSM = struct {
            old_sm: buchi.PhaseName,
            new_sm: buchi.PhaseName,
            res_phase: buchi.PhaseName,
        };
        var prev_phases = std.AutoHashMap(PrevSM, std.ArrayList(buchi.PhaseName)).init(self.gpa);
        defer {
            var it = prev_phases.iterator();
            while (it.next()) |p| {
                p.value_ptr.deinit();
            }
            prev_phases.deinit();
        }

        for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.keys(), self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.values()) |pt, res_p| {
            const entr = try prev_phases.getOrPutValue(.{
                .old_sm = pt.to_remove,
                .new_sm = pt.to_add,
                .res_phase = res_p,
            }, std.ArrayList(buchi.PhaseName).init(self.gpa));
            try entr.value_ptr.append(pt.original_phase);
        }

        while (trans.popFirst()) |edge_node| {
            const edge = edge_node.data;
            self.gpa.destroy(edge_node);

            if (!try self.pre_ma.addEdgePtr(edge)) {
                continue;
            }

            const hr_edges_opt = self.edges_by_trg.get(try self.addHead(Head{
                .state = edge.from.st.state,
                .phase = edge.from.st.phase,
                .top = edge.symbol.symbol,
            }));
            if (hr_edges_opt) |hr_edges| {
                for (hr_edges.keys()) |hr_edge| {
                    const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
                        .from = buchi.MA.Node{
                            .st = buchi.MA.StateNode{
                                .state = hr_edge.from.state,
                                .phase = hr_edge.from.phase,
                            },
                        },
                        .symbol = buchi.MA.EdgeSymbol{
                            .symbol = hr_edge.from.top,
                        },
                        .to = edge.to,
                        .accepting = edge.accepting or hr_edge.label,
                    });
                    if (!trans_set.contains(edge_ptr)) {
                        const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                        new_node.* = .{ .data = edge_ptr };
                        trans.prepend(new_node);
                        try trans_set.put(edge_ptr, {});
                    }
                }
            }

            if (rules_by_tail.get(.{ .to = edge.from.st.state, .new_top = edge.symbol.symbol })) |tail_rules| {
                for (tail_rules.items) |r| {
                    switch (r.*) {
                        .sm => {
                            const prevs = prev_phases.get(.{
                                .res_phase = edge.from.st.phase,
                                .new_sm = r.sm.new_rules,
                                .old_sm = r.sm.old_rules,
                            }) orelse continue;
                            for (prevs.items) |prev_phase| {
                                const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(prev_phase).?;
                                if (!phase.items.contains(r.sm.label)) {
                                    continue;
                                }
                                const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
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
                                if (!trans_set.contains(edge_ptr)) {
                                    const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                    new_node.* = .{ .data = edge_ptr };
                                    trans.prepend(new_node);
                                    try trans_set.put(edge_ptr, {});
                                }
                            }
                        },
                        .standard => {
                            const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(edge.from.st.phase).?;
                            if (!phase.items.contains(r.standard.label)) {
                                continue;
                            }
                            if (r.standard.new_tail == null) {
                                const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
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
                                if (!trans_set.contains(edge_ptr)) {
                                    const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                    new_node.* = .{ .data = edge_ptr };
                                    trans.prepend(new_node);
                                    try trans_set.put(edge_ptr, {});
                                }
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
                                    for (aux_edges.keys()) |edge_aux| {
                                        const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
                                            .from = buchi.MA.Node{
                                                .st = buchi.MA.StateNode{
                                                    .state = r.standard.from,
                                                    .phase = edge.from.st.phase,
                                                },
                                            },
                                            .symbol = buchi.MA.EdgeSymbol{
                                                .symbol = r.standard.top,
                                            },
                                            .to = edge_aux.to,
                                            .accepting = edge.accepting or edge_aux.accepting or self.sm_bpds.isAccepting(r.standard.from.*),
                                        });
                                        if (!trans_set.contains(edge_ptr)) {
                                            const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                            new_node.* = .{ .data = edge_ptr };
                                            trans.prepend(new_node);
                                            try trans_set.put(edge_ptr, {});
                                        }
                                    }
                                }
                            }
                        },
                    }
                }
            }
        }

        // ------------------------------

        if (root.state_initialized) {
            std.log.info("Adding default hr edges ({} edges currently): {d:.3}s", .{ self.edges.count(), @as(f64, @floatFromInt(root.state.timer.read())) / 1000000000 });
            std.log.info("Iterating over {} phases and {} rules ({} total)", .{ self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.count(), self.sm_bpds.rules.count(), self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.count() * self.sm_bpds.rules.count() });
        }

        for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phases.keys()) |phase_name| {
            const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(phase_name).?;

            rule_loop: for (self.sm_bpds.rules.keys()) |rule| {
                switch (rule) {
                    .sm => |r| {
                        if (!phase.items.contains(r.label)) {
                            continue :rule_loop;
                        }
                        const next_phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.get(.{
                            .original_phase = phase_name,
                            .to_add = r.new_rules,
                            .to_remove = r.old_rules,
                        }) orelse continue :rule_loop; // continue because it means for rule p -(r1 / r2)-> p1 there is no r1 in phase.
                        _ = try self.addEdge(Edge{
                            .from = try self.addHead(Head{
                                .state = r.from,
                                .phase = phase_name,
                                .top = r.top,
                            }),
                            .label = self.sm_bpds.isAccepting(r.from.*),
                            .to = try self.addHead(Head{
                                .state = r.to,
                                .phase = next_phase,
                                .top = r.top,
                            }),
                        });
                    },
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
        if (root.state_initialized) {
            std.log.info("Edges finish ({} edges and {} heads currently): {d:.3}s", .{ self.edges.count(), self.heads.count(), @as(f64, @floatFromInt(root.state.timer.read())) / 1000000000 });
        }
    }

    pub fn appendSchwoon(self: *@This(), new_edges: []const *const buchi.MA.Edge) !void {
        defer {
            var it = self.edges_by_trg.iterator();
            while (it.next()) |itt| {
                itt.value_ptr.deinit();
            }
            self.edges_by_trg.clearAndFree();
        }
        //  rel = self.pre_ma

        var trans = std.SinglyLinkedList(*const buchi.MA.Edge){};
        defer {
            while (trans.popFirst()) |n| {
                self.gpa.destroy(n);
            }
        }
        var trans_set = std.AutoHashMap(*const buchi.MA.Edge, void).init(self.gpa);
        defer trans_set.deinit();

        // delta_aux = self.edges

        const RuleTail = struct {
            to: buchi.StateName,
            new_top: buchi.SymbolName, // null for self-modifying rules
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
                        .new_top = r.top,
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

        for (new_edges) |edge_ptr| {
            if (!trans_set.contains(edge_ptr)) {
                const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                new_node.* = .{ .data = edge_ptr };
                trans.prepend(new_node);
                try trans_set.put(edge_ptr, {});
            }
        }

        if (root.state_initialized) {
            std.log.info("Rule map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

        const PrevSM = struct {
            old_sm: buchi.PhaseName,
            new_sm: buchi.PhaseName,
            res_phase: buchi.PhaseName,
        };
        var prev_phases = std.AutoHashMap(PrevSM, std.ArrayList(buchi.PhaseName)).init(self.gpa);
        defer {
            var it = prev_phases.iterator();
            while (it.next()) |p| {
                p.value_ptr.deinit();
            }
            prev_phases.deinit();
        }

        for (self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.keys(), self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_combiner.values()) |pt, res_p| {
            const entr = try prev_phases.getOrPutValue(.{
                .old_sm = pt.to_remove,
                .new_sm = pt.to_add,
                .res_phase = res_p,
            }, std.ArrayList(buchi.PhaseName).init(self.gpa));
            try entr.value_ptr.append(pt.original_phase);
        }

        for (self.edges.values()) |edge_ptr| {
            const edge = edge_ptr.*;
            const gop = try self.edges_by_trg.getOrPut(edge.to);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge_ptr, {});
        }

        while (trans.popFirst()) |edge_node| {
            const edge = edge_node.data;
            self.gpa.destroy(edge_node);

            if (!try self.pre_ma.addEdgePtr(edge)) {
                continue;
            }
            switch (edge.from) {
                .st => {},
                .int => continue,
            }

            const hr_edges_opt = self.edges_by_trg.get(try self.addHead(Head{
                .state = edge.from.st.state,
                .phase = edge.from.st.phase,
                .top = edge.symbol.symbol,
            }));
            if (hr_edges_opt) |hr_edges| {
                for (hr_edges.keys()) |hr_edge| {
                    const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
                        .from = buchi.MA.Node{
                            .st = buchi.MA.StateNode{
                                .state = hr_edge.from.state,
                                .phase = hr_edge.from.phase,
                            },
                        },
                        .symbol = buchi.MA.EdgeSymbol{
                            .symbol = hr_edge.from.top,
                        },
                        .to = edge.to,
                        .accepting = edge.accepting or hr_edge.label,
                    });
                    if (!trans_set.contains(edge_ptr) and !self.pre_ma.edge_set.contains(edge_ptr)) {
                        const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                        new_node.* = .{ .data = edge_ptr };
                        trans.prepend(new_node);
                        try trans_set.put(edge_ptr, {});
                    }
                }
            }

            if (rules_by_tail.get(.{ .to = edge.from.st.state, .new_top = edge.symbol.symbol })) |tail_rules| {
                for (tail_rules.items) |r| {
                    switch (r.*) {
                        .sm => {
                            const prevs = prev_phases.get(.{
                                .res_phase = edge.from.st.phase,
                                .new_sm = r.sm.new_rules,
                                .old_sm = r.sm.old_rules,
                            }) orelse continue;
                            for (prevs.items) |prev_phase| {
                                const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(prev_phase).?;
                                if (!phase.items.contains(r.sm.label)) {
                                    continue;
                                }
                                const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
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
                                if (!trans_set.contains(edge_ptr) and !self.pre_ma.edge_set.contains(edge_ptr)) {
                                    const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                    new_node.* = .{ .data = edge_ptr };
                                    trans.prepend(new_node);
                                    try trans_set.put(edge_ptr, {});
                                }
                            }
                        },
                        .standard => {
                            const phase = self.sm_bpds.sm_gbpds.sm_pds_proc.?.phase_names.phase_values.get(edge.from.st.phase).?;
                            if (!phase.items.contains(r.standard.label)) {
                                continue;
                            }
                            if (r.standard.new_tail == null) {
                                const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
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
                                if (!trans_set.contains(edge_ptr) and !self.pre_ma.edge_set.contains(edge_ptr)) {
                                    const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                    new_node.* = .{ .data = edge_ptr };
                                    trans.prepend(new_node);
                                    try trans_set.put(edge_ptr, {});
                                }
                            } else {
                                const aux_edges_opt = self.pre_ma.edges_by_head.get(.{
                                    .from = edge.to,
                                    .symbol = buchi.MA.EdgeSymbol{ .symbol = r.standard.new_tail.? },
                                });
                                if (aux_edges_opt) |aux_edges| {
                                    for (aux_edges.keys()) |edge_aux| {
                                        const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
                                            .from = buchi.MA.Node{
                                                .st = buchi.MA.StateNode{
                                                    .state = r.standard.from,
                                                    .phase = edge.from.st.phase,
                                                },
                                            },
                                            .symbol = buchi.MA.EdgeSymbol{
                                                .symbol = r.standard.top,
                                            },
                                            .to = edge_aux.to,
                                            .accepting = edge.accepting or edge_aux.accepting or self.sm_bpds.isAccepting(r.standard.from.*),
                                        });
                                        if (!trans_set.contains(edge_ptr) and !self.pre_ma.edge_set.contains(edge_ptr)) {
                                            const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                            new_node.* = .{ .data = edge_ptr };
                                            trans.prepend(new_node);
                                            try trans_set.put(edge_ptr, {});
                                        }
                                    }
                                }

                                const aux_edges_opt_star = self.pre_ma.edges_by_head.get(.{
                                    .from = edge.to,
                                    .symbol = buchi.MA.EdgeSymbol{ .star = {} },
                                });
                                if (aux_edges_opt_star) |aux_edges| {
                                    for (aux_edges.keys()) |edge_aux| {
                                        const edge_ptr = try self.pre_ma.storeEdge(buchi.MA.Edge{
                                            .from = buchi.MA.Node{
                                                .st = buchi.MA.StateNode{
                                                    .state = r.standard.from,
                                                    .phase = edge.from.st.phase,
                                                },
                                            },
                                            .symbol = buchi.MA.EdgeSymbol{
                                                .symbol = r.standard.top,
                                            },
                                            .to = edge_aux.to,
                                            .accepting = edge.accepting or edge_aux.accepting or self.sm_bpds.isAccepting(r.standard.from.*),
                                        });
                                        if (!trans_set.contains(edge_ptr) and !self.pre_ma.edge_set.contains(edge_ptr)) {
                                            const new_node = try self.gpa.create(std.SinglyLinkedList(*const buchi.MA.Edge).Node);
                                            new_node.* = .{ .data = edge_ptr };
                                            trans.prepend(new_node);
                                            try trans_set.put(edge_ptr, {});
                                        }
                                    }
                                }
                            }
                        },
                    }
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
    pub fn findRepeatingHeads(self: *@This(), gpa: std.mem.Allocator) ![]SCC {
        var index: u32 = 0;

        var stack = std.ArrayList(*Head).init(gpa);
        defer stack.deinit();

        var sccs = std.ArrayList(SCC).init(gpa);
        defer sccs.deinit();

        for (self.edges.values()) |edge| {
            const src = edge.from;

            const gop = try self.edges_by_src.getOrPut(src);
            if (!gop.found_existing) {
                gop.value_ptr.* = std.AutoArrayHashMap(*const Edge, void).init(self.gpa);
            }
            try gop.value_ptr.put(edge, {});
        }

        if (root.state_initialized) {
            std.log.info("source map constructed: {d:.3}s", .{@as(f64, @floatFromInt(root.state.timer.read())) / 1000000000});
        }

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
            for (edge_list.keys()) |edge| {
                const to = edge.to;
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

            var heads_count: usize = 0;
            if (stack.items.len > 0) {
                var i = stack.items.len - 1;
                while (i >= 0) : (i -= 1) {
                    heads_count += 1;
                    stack.items[i].*.on_stack = false;
                    if (stack.items[i] == head) break;
                }
            }
            const head_items = try gpa.dupe(*Head, stack.items[stack.items.len - heads_count ..]);
            errdefer gpa.free(head_items);
            stack.shrinkRetainingCapacity(stack.items.len - heads_count);

            // var heads = std.ArrayList(*const Head).init(gpa);
            // defer heads.deinit();
            // while (stack.pop()) |h| {
            //     h.*.on_stack = false;
            //     try heads.append(h);

            //     if (h == head) break;
            // }

            var accepting = false;

            is_acc: for (head_items) |h1| {
                for (head_items) |h2| {
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
                    .heads = head_items,
                };
                try sccs.append(scc);
            } else {
                gpa.free(head_items);
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

pub fn build_hr_pre(gpa: std.mem.Allocator, ma: *buchi.MA, sccs: []const HeadReachabilityGraph.SCC) ![]*const buchi.MA.Edge {
    var count: usize = 0;

    for (sccs) |scc| {
        for (scc.heads) |_| {
            count += 1;
        }
    }
    const res = try gpa.alloc(*const buchi.MA.Edge, count + 1);

    const acc_node = buchi.MA.Node{
        .int = .{ .id = 0, .accepting = true },
    };
    res[0] = try ma.storeEdge(.{
        .from = acc_node,
        .to = acc_node,
        .accepting = false,
        .symbol = .{ .star = {} },
    });

    var i: usize = 1;

    for (sccs) |scc| {
        for (scc.heads) |head| {
            res[i] = try ma.storeEdge(.{
                .from = .{ .st = .{
                    .state = head.state,
                    .phase = head.phase,
                } },
                .to = acc_node,
                .accepting = false,
                .symbol = .{ .symbol = head.top },
            });
            i += 1;
        }
    }
    return res;
}
