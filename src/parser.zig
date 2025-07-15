const std = @import("std");
const mecha = @import("mecha");

pub const RuleType = enum { internal, sm, call, ret };

pub const Conf = struct {
    state: []const u8,
    stack: []const []const u8,
    phase: []const []const u8,
};

pub const Rule = struct {
    name: []const u8,
    typ: RuleType,
    from: []const u8,
    top: ?[]const u8 = null,
    to: []const u8,
    new_top: ?[]const u8 = null,
    new_tail: ?[]const u8 = null,
    sm_l: ?[]const []const u8 = null,
    sm_r: ?[]const []const u8 = null,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (fmt.len != 0) {
            std.fmt.invalidFmtError(fmt, self);
        }
        return switch (self.typ) {
            RuleType.internal => writer.print("{s} {s} \\--> {s} {s} {s}", .{ self.from, self.top.?, self.to, self.new_top orelse "-", self.new_tail orelse "-" }),
            RuleType.call => writer.print("{s} {s} \\-call-> {s} {s} {s}", .{ self.from, self.top.?, self.to, self.new_top.?, self.new_tail.? }),
            RuleType.ret => writer.print("{s} {s} \\-ret-> {s}", .{ self.from, self.top.?, self.to }),
            RuleType.sm => {
                try writer.print("{s} \\--(", .{self.from});
                for (self.sm_l.?, 0..) |r, i| {
                    if (i > 0) {
                        try writer.print(", ", .{});
                    }
                    try writer.print("{s}", .{r});
                }
                try writer.print(")-/-(", .{});
                for (self.sm_r.?, 0..) |r, i| {
                    if (i > 0) {
                        try writer.print(", ", .{});
                    }
                    try writer.print("{s}", .{r});
                }
                try writer.print(")--> {s}", .{self.to});
            },
        };
    }
};

pub const SM_PDS = struct {
    states: [][]const u8,
    alphabet: [][]const u8,
    rules: []const Rule,
};

const JsonError = error{
    InvalidSMRule,
};

pub fn parseJsonFromPython(allocator: std.mem.Allocator, filename: []const u8) !ParsedSMPDS {
    var file = try std.fs.cwd().openFile(filename, .{});
    defer file.close();

    var reader = std.json.reader(allocator, file.reader());

    const val = try std.json.parseFromTokenSourceLeaky(std.json.Value, allocator, &reader, .{});

    const smpds = val.array.items[0];
    var states = try allocator.alloc([]const u8, smpds.array.items[0].array.items.len);

    for (smpds.array.items[0].array.items, 0..) |s, j| {
        states[j] = try allocator.dupe(u8, s.string);
    }

    var alphabet = try allocator.alloc([]const u8, smpds.array.items[1].array.items.len);
    for (smpds.array.items[1].array.items, 0..) |s, j| {
        alphabet[j] = try allocator.dupe(u8, s.string);
    }

    var rules = try allocator.alloc(Rule, smpds.array.items[2].object.count() + smpds.array.items[3].object.count());

    for (smpds.array.items[2].object.keys(), 0..) |name, j| {
        const r = smpds.array.items[2].object.get(name).?.array;

        if (r.items.len != 5) {
            std.log.err("Invalid JSON provided: Rule {s} does not contains 5 elements (p.1 g.2 -> p.3 g.4 label.5)", .{name});
            return JsonError.InvalidSMRule;
        }

        var new_top: ?[]const u8 = undefined;
        var new_tail: ?[]const u8 = undefined;
        if (r.items[3].string.len == 0) {
            new_top = null;
            new_tail = null;
        } else {
            if (std.mem.indexOf(u8, r.items[3].string, " ")) |ind| {
                new_top = try allocator.dupe(u8, r.items[3].string[0..ind]);
                new_tail = try allocator.dupe(u8, r.items[3].string[ind + 1 ..]);
            } else {
                new_top = try allocator.dupe(u8, r.items[3].string);
                new_tail = null;
            }
        }

        rules[j] = Rule{
            .name = try allocator.dupe(u8, name),
            .from = try allocator.dupe(u8, r.items[0].string),
            .to = try allocator.dupe(u8, r.items[2].string),
            .top = try allocator.dupe(u8, r.items[1].string),
            .new_top = new_top,
            .new_tail = new_tail,
            .typ = if (std.mem.eql(u8, r.items[4].string, "call")) RuleType.call else if (std.mem.eql(u8, r.items[4].string, "int")) RuleType.internal else if (std.mem.eql(u8, r.items[4].string, "ret")) RuleType.ret else {
                std.log.err("Invalid JSON provided: Rule {s} is labelled with unknown label '{s}'", .{ name, r.items[4].string });
                return JsonError.InvalidSMRule;
            },
        };
    }

    for (smpds.array.items[3].object.keys(), smpds.array.items[2].object.keys().len..) |name, j| {
        const r = smpds.array.items[3].object.get(name).?.array;

        const sm_l = blk: switch (r.items[1].array.items[0]) {
            .string => |s| {
                break :blk try allocator.dupe([]const u8, &.{s});
            },
            .array => |arr| {
                var sm_l_tmp = try allocator.alloc([]const u8, arr.items.len);
                for (arr.items, 0..) |r_name, k| {
                    sm_l_tmp[k] = try allocator.dupe(u8, r_name.string);
                }
                break :blk sm_l_tmp;
            },
            else => return JsonError.InvalidSMRule,
        };
        const sm_r = blk: switch (r.items[1].array.items[1]) {
            .string => |s| {
                break :blk try allocator.dupe([]const u8, &.{s});
            },
            .array => |arr| {
                var sm_r_tmp = try allocator.alloc([]const u8, arr.items.len);
                for (arr.items, 0..) |r_name, k| {
                    sm_r_tmp[k] = try allocator.dupe(u8, r_name.string);
                }
                break :blk sm_r_tmp;
            },
            else => return JsonError.InvalidSMRule,
        };

        rules[j] = Rule{
            .name = try allocator.dupe(u8, name),
            .from = try allocator.dupe(u8, r.items[0].string),
            .to = try allocator.dupe(u8, r.items[2].string),
            .typ = RuleType.sm,
            .sm_l = sm_l,
            .sm_r = sm_r,
        };
    }

    const res_smpds = SM_PDS{ .states = states, .alphabet = alphabet, .rules = rules };

    const caret_str = val.array.items[1].string;
    const res = try formulaRef.parse(allocator, caret_str);
    var caret: *const RawCaret = undefined;
    switch (res.value) {
        .ok => |caret_raw| {
            caret = caret_raw;
        },
        .err => |_| {
            const pos = getErrorPosition(caret_str, res.index);
            const snippet_length = @min(caret_str.len - res.index, 5);
            std.debug.print("Parsing CTL Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, caret_str[res.index..][0..snippet_length] });
            return CaretParseError.StringParseError;
        },
    }

    switch (val.array.items[2]) {
        .array => {},
        else => {
            std.log.err("Initial configuration is not an array\n", .{});
            return error.StringParseError;
        },
    }

    const init = val.array.items[2];
    switch (init.array.items[1]) {
        .string => {},
        else => {
            std.log.err("Initial configuration stack is not a whitespace-separated string\n", .{});
            return error.StringParseError;
        },
    }
    var seq = std.mem.splitSequence(u8, init.array.items[1].string, " ");

    var stack = std.ArrayList([]const u8).init(allocator);
    var itt: ?[]const u8 = seq.first();
    while (itt) |it| {
        try stack.append(try allocator.dupe(u8, it));
        itt = seq.next();
    }

    var phase = try allocator.alloc([]const u8, init.array.items[2].array.items.len);
    for (init.array.items[2].array.items, 0..) |rule, k| {
        phase[k] = try allocator.dupe(u8, rule.string);
    }

    const res_init = Conf{
        .state = init.array.items[0].string,
        .stack = try stack.toOwnedSlice(),
        .phase = phase,
    };

    return ParsedSMPDS{
        .smpds = res_smpds,
        .caret = caret,
        .init = res_init,
    };
}

pub const RawCaret = union(enum) {
    ap: []const u8,
    top,
    bot,
    lnot: *const RawCaret,
    lor: struct {
        left: *const RawCaret,
        right: *const RawCaret,
    },
    ug: struct {
        left: *const RawCaret,
        right: *const RawCaret,
    },
    ua: struct {
        left: *const RawCaret,
        right: *const RawCaret,
    },
    uc: struct {
        left: *const RawCaret,
        right: *const RawCaret,
    },
    xg: *const RawCaret,
    xa: *const RawCaret,
    xc: *const RawCaret,
};

fn fromStr(comptime parser: mecha.Parser([]const u8)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_str: mecha.Result([]const u8) = try parser.parse(allocator, str);
            return switch (res_str.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .ap = res_str.value.ok };
                    break :blk Res.ok(res_str.index, caret);
                },
                .err => Res.err(res_str.index),
            };
        }
    }.parse };
}

fn fromLor(comptime parser: mecha.Parser(BinaryOp)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(BinaryOp) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .lor = .{ .left = res_comb.value.ok.@"0", .right = res_comb.value.ok.@"1" } };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromLnot(comptime parser: mecha.Parser(*const RawCaret)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const RawCaret) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .lnot = res_comb.value.ok };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromUG(comptime parser: mecha.Parser(BinaryOp)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(BinaryOp) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .ug = .{ .left = res_comb.value.ok.@"0", .right = res_comb.value.ok.@"1" } };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromUA(comptime parser: mecha.Parser(BinaryOp)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(BinaryOp) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .ua = .{ .left = res_comb.value.ok.@"0", .right = res_comb.value.ok.@"1" } };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromUC(comptime parser: mecha.Parser(BinaryOp)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(BinaryOp) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .uc = .{ .left = res_comb.value.ok.@"0", .right = res_comb.value.ok.@"1" } };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromXG(comptime parser: mecha.Parser(*const RawCaret)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const RawCaret) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .xg = res_comb.value.ok };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromXA(comptime parser: mecha.Parser(*const RawCaret)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const RawCaret) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .xa = res_comb.value.ok };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn fromXC(comptime parser: mecha.Parser(*const RawCaret)) mecha.Parser(*const RawCaret) {
    const Res = mecha.Result(*const RawCaret);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(*const RawCaret) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    const caret = try allocator.create(RawCaret);
                    caret.* = RawCaret{ .xc = res_comb.value.ok };
                    break :blk Res.ok(res_comb.index, caret);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

const caret_top: RawCaret = .top;
const caret_bot: RawCaret = .bot;

const id_grammar = mecha.oneOf(.{
    mecha.combine(.{
        mecha.ascii.range('a', 'z'),
        mecha.oneOf(.{
            mecha.ascii.range('a', 'z'),
            mecha.ascii.range('A', 'Z'),
            mecha.ascii.char('_'),
            mecha.ascii.range('0', '9'),
        }).many(.{}),
    }).asStr(),
    mecha.combine(.{
        mecha.ascii.char('@').discard(),
        mecha.ascii.char('"').discard(),
        chars,
        mecha.ascii.char('"').discard(),
    }),
});
const chars = char.many(.{}).asStr();
const char = mecha.oneOf(.{
    mecha.ascii.not(mecha.oneOf(.{ mecha.ascii.char('"'), mecha.ascii.char('\\') })),
    mecha.combine(.{
        mecha.ascii.char('\\').discard(),
        escape,
    }),
});

const escape = mecha.oneOf(.{
    mecha.ascii.char('"'),
    mecha.ascii.char('\\'),
    mecha.ascii.char('/'),
    mecha.ascii.char('b'),
    mecha.ascii.char('f'),
    mecha.ascii.char('n'),
    mecha.ascii.char('r'),
    mecha.ascii.char('t'),
});

const ap = fromStr(id_grammar);

const BinaryOp = std.meta.Tuple(&.{ *const RawCaret, *const RawCaret });

const formulaRef = mecha.ref(formulaRefFn);

const formulaClosed = mecha.combine(.{ token(mecha.string("(")), formulaRef, ws, token(mecha.string(")")) });

const formula1 = mecha.oneOf(.{
    token(mecha.string("True")).mapConst(&caret_top),
    token(mecha.string("False")).mapConst(&caret_bot),
    ap,
    formulaClosed,
});

const formulaX = mecha.oneOf(.{
    fromXG(mecha.combine(.{ token(mecha.string("Xg")), mecha.ref(formulaXRef) })),
    fromXA(mecha.combine(.{ token(mecha.string("Xa")), mecha.ref(formulaXRef) })),
    fromXC(mecha.combine(.{ token(mecha.string("Xc")), mecha.ref(formulaXRef) })),
    fromLnot(mecha.combine(.{ token(mecha.string("~")), mecha.ref(formulaXRef) })),
    formula1,
});

fn formulaXRef() mecha.Parser(*const RawCaret) {
    return formulaX;
}

const formula2 = mecha.oneOf(.{
    formulaX,
});
fn formula2Ref() mecha.Parser(*const RawCaret) {
    return formula2;
}

const formula3 = mecha.oneOf(.{
    fromLor(mecha.combine(.{ formula2, ws, token(mecha.string("||")), mecha.ref(formula3Ref) })),
    fromUG(mecha.combine(.{ formula2, ws, token(mecha.string("Ug")), mecha.ref(formula3Ref) })),
    fromUA(mecha.combine(.{ formula2, ws, token(mecha.string("Ua")), mecha.ref(formula3Ref) })),
    fromUC(mecha.combine(.{ formula2, ws, token(mecha.string("Uc")), mecha.ref(formula3Ref) })),
    formula2,
});
fn formula3Ref() mecha.Parser(*const RawCaret) {
    return formula3;
}

fn formulaRefFn() mecha.Parser(*const RawCaret) {
    return formula3;
}

const fullCtlFormula = mecha.combine(.{ formulaRef, mecha.eos });

fn token(comptime parser: anytype) mecha.Parser(void) {
    return mecha.combine(.{ parser.discard(), ws });
}

const comment = mecha.combine(.{ mecha.string("//").discard(), mecha.utf8.not(mecha.utf8.char(0x000A)).many(.{}).discard(), mecha.utf8.char(0x000A) });
const ml_comment: mecha.Parser(u21) = mecha.combine(.{
    mecha.string("/*").discard(),
    mecha.oneOf(.{
        mecha.ascii.not(mecha.ascii.char('*')).asStr(),
        mecha.combine(.{ mecha.ascii.char('*').many(.{ .min = 1 }), mecha.ascii.not(mecha.ascii.char('/')) }).asStr(),
    }).many(.{}).discard(),
    mecha.ascii.char('*').many(.{ .min = 1 }).discard(),
    mecha.utf8.char('/'),
});

const ws = mecha.oneOf(.{
    comment,
    ml_comment,
    mecha.utf8.char(0x0020),
    mecha.utf8.char(0x000A),
    mecha.utf8.char(0x000D),
    mecha.utf8.char(0x0009),
}).many(.{ .collect = false }).discard();

fn PopRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.internal,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn StandardRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.internal,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                    .new_top = res_comb.value.ok.@"4",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn PushRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.internal,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                    .new_top = res_comb.value.ok.@"4",
                    .new_tail = res_comb.value.ok.@"5",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn SMRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, [][]const u8, [][]const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, [][]const u8, [][]const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => blk: {
                    std.mem.sort([]const u8, res_comb.value.ok.@"2", {}, lt);
                    std.mem.sort([]const u8, res_comb.value.ok.@"3", {}, lt);
                    break :blk Res.ok(res_comb.index, Rule{
                        .typ = RuleType.sm,
                        .name = res_comb.value.ok.@"0",
                        .from = res_comb.value.ok.@"1",
                        .sm_l = res_comb.value.ok.@"2",
                        .sm_r = res_comb.value.ok.@"3",
                        .to = res_comb.value.ok.@"4",
                    });
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn CallRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.call,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                    .new_top = res_comb.value.ok.@"4",
                    .new_tail = res_comb.value.ok.@"5",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn RetRuleParser(comptime parser: mecha.Parser(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 }))) mecha.Parser(Rule) {
    const Res = mecha.Result(Rule);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            const res_comb: mecha.Result(std.meta.Tuple(&.{ []const u8, []const u8, []const u8, []const u8 })) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => Res.ok(res_comb.index, Rule{
                    .typ = RuleType.ret,
                    .name = res_comb.value.ok.@"0",
                    .from = res_comb.value.ok.@"1",
                    .top = res_comb.value.ok.@"2",
                    .to = res_comb.value.ok.@"3",
                }),
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

fn SMPDSParser(comptime parser: mecha.Parser([]Rule)) mecha.Parser(SM_PDS) {
    const Res = mecha.Result(SM_PDS);
    return .{ .parse = struct {
        fn parse(allocator: std.mem.Allocator, str: []const u8) !Res {
            var states = std.StringArrayHashMap(void).init(allocator);
            var alphabet = std.StringArrayHashMap(void).init(allocator);
            var rules = std.ArrayList(Rule).init(allocator);

            const res_comb: mecha.Result([]Rule) = try parser.parse(allocator, str);

            return switch (res_comb.value) {
                .ok => |val| blk: {
                    for (val) |rule| {
                        try rules.append(rule);
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
                    const states_sorted = try allocator.dupe([]const u8, states.keys());
                    std.mem.sort([]const u8, states_sorted, {}, lt);
                    const alphabet_sorted = try allocator.dupe([]const u8, alphabet.keys());
                    std.mem.sort([]const u8, alphabet_sorted, {}, lt);
                    const smdpds = SM_PDS{
                        .states = states_sorted,
                        .alphabet = alphabet_sorted,
                        .rules = rules.items,
                    };
                    break :blk Res.ok(res_comb.index, smdpds);
                },
                .err => Res.err(res_comb.index),
            };
        }
    }.parse };
}

const id_sequence = id_grammar.many(.{ .separator = ws });

const sm_pds_rule_grammar = mecha.oneOf(.{
    RetRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("+>")), id_grammar, ws, token(mecha.string(";")) })),
    CallRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("+>")), id_grammar, ws, id_grammar, ws, id_grammar, ws, token(mecha.string(";")) })),

    PopRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("->")), id_grammar, ws, token(mecha.string(";")) })),
    StandardRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("->")), id_grammar, ws, id_grammar, ws, token(mecha.string(";")) })),
    PushRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, id_grammar, ws, token(mecha.string("->")), id_grammar, ws, id_grammar, ws, id_grammar, ws, token(mecha.string(";")) })),
    SMRuleParser(mecha.combine(.{ id_grammar, ws, token(mecha.string(":")), id_grammar, ws, token(mecha.string("-(")), id_sequence, ws, token(mecha.string("/")), id_sequence, ws, token(mecha.string(")->")), id_grammar, ws, token(mecha.string(";")) })),
});

const sm_pds_grammar = mecha.combine(.{
    ws,
    init_state_grammar,
    mecha.combine(.{ token(mecha.string("caret")), token(mecha.string("{")), formulaRef, ws, token(mecha.string("}")) }),
    SMPDSParser(sm_pds_rule_grammar.many(.{ .separator = ws })),
}).map(struct {
    fn map(res: std.meta.Tuple(&.{ Conf, *const RawCaret, SM_PDS })) ParsedSMPDS {
        return ParsedSMPDS{
            .init = res.@"0",
            .caret = res.@"1",
            .smpds = res.@"2",
        };
    }
}.map);

const init_state_grammar = mecha.combine(.{
    token(mecha.string("init")),
    id_grammar,
    ws,
    id_sequence,
    ws,
    token(mecha.string("#")),
    id_sequence,
    ws,
    token(mecha.string(";")),
})
    .map(struct {
    fn map(res: std.meta.Tuple(&.{ []const u8, [][]const u8, [][]const u8 })) Conf {
        return Conf{
            .state = res.@"0",
            .stack = res.@"1",
            .phase = res.@"2",
        };
    }
}.map);

pub const ParsedSMPDS = struct {
    init: Conf,
    caret: *const RawCaret,
    smpds: SM_PDS,
};

fn lt(_: void, lhs: []const u8, rhs: []const u8) bool {
    return std.mem.order(u8, lhs, rhs) == .lt;
}

pub const ErrorPos = struct {
    line: usize,
    col: usize,
};

fn getErrorPosition(str: []const u8, pos: usize) ErrorPos {
    var start_pos: usize = 0;
    var line_counter: usize = 1;
    while (true) {
        const nl_pos = std.mem.indexOfPos(u8, str, start_pos, "\n") orelse str.len;
        if (pos <= nl_pos) {
            return ErrorPos{
                .line = line_counter,
                .col = pos - start_pos + 1,
            };
        }
        start_pos = nl_pos + 1;
        line_counter += 1;
        if (nl_pos == str.len) {
            break;
        }
    }
    return ErrorPos{ .line = line_counter, .col = 1 };
}

pub const SmpdsFile = struct {
    arena: std.heap.ArenaAllocator,
    filename: []const u8,

    pub fn open(allocator: std.mem.Allocator, filename: []const u8) SmpdsFile {
        return SmpdsFile{
            .arena = std.heap.ArenaAllocator.init(allocator),
            .filename = filename,
        };
    }

    pub fn close(self: *@This()) void {
        self.arena.deinit();
    }

    /// This struct still owns the memory of the result, if you need to close the file, then first deep copy the result to other place
    pub fn parse(self: *@This()) !ParsedSMPDS {
        var file = try std.fs.cwd().openFile(self.filename, .{});
        defer file.close();

        var buf_reader = std.io.bufferedReader(file.reader());
        var in_stream = buf_reader.reader();

        var file_contents = std.ArrayList(u8).init(self.arena.allocator());
        try file_contents.ensureTotalCapacity((try file.stat()).size);

        var buf: [1024]u8 = undefined;
        while (try in_stream.readUntilDelimiterOrEof(&buf, '\n')) |line| {
            try file_contents.appendSlice(line);
            try file_contents.append('\n');
        }
        // std.debug.print("{s}\n---\n", .{file_contents.items});
        const sm_dpds_res: mecha.Result(ParsedSMPDS) = try sm_pds_grammar.parse(self.arena.allocator(), file_contents.items);
        switch (sm_dpds_res.value) {
            .ok => |val| {
                return val;
            },
            .err => |_| {
                const pos = getErrorPosition(file_contents.items, sm_dpds_res.index);
                const snippet_length = @min(file_contents.items.len - sm_dpds_res.index, 5);
                std.debug.print("Parsing SM-PDS Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, file_contents.items[sm_dpds_res.index..][0..snippet_length] });
                return CaretParseError.StringParseError;
            },
        }
    }
};

pub const CaretParseError = error{
    APNotInStates,
    StringParseError,
};

test "caret formula" {
    const str = "~(True Ug ( ~ p1 ) )";
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const res = try fullCtlFormula.parse(allocator, str);
    switch (res.value) {
        .ok => |_| {},
        .err => {
            const pos = getErrorPosition(str, res.index);

            const snippet_length = @min(str.len - res.index, 5);
            std.debug.print("Parsing Caret Error at line {d}, column {d}:\n{s}...\n", .{ pos.line, pos.col, str[res.index..][0..snippet_length] });
            try std.testing.expect(false);
        },
    }
}

test "smpds file" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var file = SmpdsFile.open(allocator, "examples/example.smpds");
    _ = try file.parse();
}

test "rule parser" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var res: mecha.Result(Rule) = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 -> p2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.internal);
            try std.testing.expectEqual(val.new_top, null);
            try std.testing.expectEqual(val.new_tail, null);
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 -> p2 g2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.internal);
            try std.testing.expectEqualStrings(val.new_top.?, "g2");
            try std.testing.expectEqual(val.new_tail, null);
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 -> p2 g2 g3;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.internal);
            try std.testing.expectEqualStrings(val.new_top.?, "g2");
            try std.testing.expectEqualStrings(val.new_tail.?, "g3");
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 -( r1 r2 r3 / r4 r5 )-> p2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqual(val.top, null);
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.sm);
            try std.testing.expectEqual(val.new_top, null);
            try std.testing.expectEqual(val.new_tail, null);
            const correct_l: []const []const u8 = &.{ "r1", "r2", "r3" };
            const correct_r: []const []const u8 = &.{ "r4", "r5" };
            try std.testing.expectEqualDeep(val.sm_l.?, correct_l);
            try std.testing.expectEqualDeep(val.sm_r.?, correct_r);
        },
        .err => |_| {
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 +> p2 g2 g1;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.call);
            try std.testing.expectEqualStrings(val.new_top.?, "g2");
            try std.testing.expectEqualStrings(val.new_tail.?, "g1");
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            std.debug.print("Error at {any}\n", .{res.index});
            try std.testing.expect(false);
        },
    }

    res = try sm_pds_rule_grammar.parse(allocator, "r1: p1 g1 +> p2;");
    switch (res.value) {
        .ok => |val| {
            try std.testing.expectEqualStrings(val.name, "r1");
            try std.testing.expectEqualStrings(val.from, "p1");
            try std.testing.expectEqualStrings(val.top.?, "g1");
            try std.testing.expectEqualStrings(val.to, "p2");
            try std.testing.expectEqual(val.typ, RuleType.ret);
            try std.testing.expectEqual(val.new_top, null);
            try std.testing.expectEqual(val.new_tail, null);
            try std.testing.expectEqual(val.sm_l, null);
            try std.testing.expectEqual(val.sm_r, null);
        },
        .err => |_| {
            std.debug.print("Error at {any}\n", .{res.index});
            try std.testing.expect(false);
        },
    }

    const example =
        \\// this is example
        \\ init p3 g1 # r1 r2 r4;
        \\
        \\ caret {p1 || Xg p2}
        \\ r1: p1 g1 ->
        \\      // the parser should read comments anywhere
        \\      p2 g2;
        \\ r2: p1 g1 -> p2 g2 g3;
        \\ // inclduing here
        \\
        \\ r11: p3 g1 -> p5 g2; // and here
        \\
        \\ r12: p4 g1 +> p6 g2 g3;
        \\ r13: p5 g1 -> p3 g2;
        \\ r14: p6 g1 -> p6 g2 g3;
        \\ /**********
        \\ * we should be able to
        \\ * write multi**-line comment
        \\ * like this**
        \\ ***************/
    ;

    const sm_pds_res: mecha.Result(ParsedSMPDS) = try sm_pds_grammar.parse(allocator, example);
    switch (sm_pds_res.value) {
        .ok => |val_conf| {
            const init: Conf = .{
                .state = "p3",
                .stack = &.{"g1"},
                .phase = &.{ "r1", "r2", "r4" },
            };
            try std.testing.expectEqualDeep(init, val_conf.init);
            const val = val_conf;
            const states1: []const []const u8 = &.{ "p1", "p2", "p3", "p4", "p5", "p6" };
            const alphabet1: []const []const u8 = &.{ "g1", "g2", "g3" };
            try std.testing.expectEqualDeep(states1, val.smpds.states);
            try std.testing.expectEqualDeep(alphabet1, val.smpds.alphabet);
            try std.testing.expectEqual(6, val.smpds.rules.len);
            try std.testing.expectEqualDeep(&RawCaret{ .lor = .{
                .left = &RawCaret{ .ap = "p1" },
                .right = &RawCaret{
                    .xg = &RawCaret{ .ap = "p2" },
                },
            } }, val.caret);
        },
        .err => |_| {
            std.debug.print("Error at {any}\n", .{getErrorPosition(example, sm_pds_res.index)});
            try std.testing.expect(false);
        },
    }
}

test "unprocessed printing" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    {
        const r1 = Rule{
            .name = "r1",
            .typ = RuleType.internal,
            .from = "p1",
            .to = "p2",
            .top = "g1",
            .new_top = "g2",
        };
        _ = &r1;
        const str = try std.fmt.allocPrint(allocator, "{}", .{r1});
        const test_str = "p1 g1 \\--> p2 g2 -";
        try std.testing.expectEqualStrings(str, test_str);
    }

    {
        const r1 = Rule{
            .name = "r1",
            .typ = RuleType.call,
            .from = "p1",
            .to = "p2",
            .top = "g1",
            .new_top = "g2",
            .new_tail = "g3",
        };
        _ = &r1;
        const str = try std.fmt.allocPrint(allocator, "{}", .{r1});
        const test_str = "p1 g1 \\-call-> p2 g2 g3";
        try std.testing.expectEqualStrings(str, test_str);
    }

    {
        const r1 = Rule{
            .name = "r1",
            .typ = RuleType.sm,
            .from = "p1",
            .to = "p2",
            .sm_l = &[_][]const u8{"r1"},
            .sm_r = &[_][]const u8{ "r1", "r2", "r3" },
        };
        _ = &r1;
        const str = try std.fmt.allocPrint(allocator, "{}", .{r1});
        const test_str = "p1 \\--(r1)-/-(r1, r2, r3)--> p2";
        try std.testing.expectEqualStrings(str, test_str);
    }
}

test "python parse" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const parsed = try parseJsonFromPython(allocator, "examples/python_example.json");

    _ = parsed;
}
