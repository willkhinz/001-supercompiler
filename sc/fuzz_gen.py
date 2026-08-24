"""Differential fuzzer: random well-typed SC-Lang programs with effects.

Every generated program is run three ways:
  1. reference interpreter (independent oracle)
  2. unoptimized bytecode VM
  3. supercompiled bytecode VM
Observable behavior compared exactly:
  - printed output sequence (strings)
  - termination status: ok / exc / timeout
  - final value or exception payload (normalized; closures/boxes -> tags)
  - mutation trace: ordered sequence of values written via set-box!
    (the optimizer never eliminates/reorders box writes, rule E1, so the
    write-value sequence must match exactly)

Programs are guaranteed to terminate: recursion only via a fuel counter.
"""
from __future__ import annotations

import random

from sc.semantics import Pair, Box, Closure, Sym

# ---------------------------------------------------------------- generator


class Gen:
    def __init__(self, rng):
        self.r = rng
        self.n = 0

    def fresh(self, base="v"):
        self.n += 1
        return "%s%d" % (base, self.n)


def S(name):
    """Variable reference as a symbol node (pretty-prints bare)."""
    return ("sym", name)


import os

HIGH_FUEL = bool(os.environ.get("SC_FUZZ_HIGH"))


def gen_program(seed):
    rng = random.Random(seed)
    g = Gen(rng)
    funcs = []
    nfuncs = rng.randint(0, 4)
    for i in range(nfuncs):
        funcs.append(_gen_func(g, i))
    body = _gen_expr(g, funcs, scope=set(), fuel_var=None,
                     depth=0, budget=rng.randint(14, 46))
    parts = []
    for name, params, fbody in funcs:
        parts.append(["define", [name] + params, fbody])
    # guarantee every function is actually called from main
    rr = rng
    for i, (name, params, _fb) in enumerate(funcs):
        lo, hi = (24, 48) if HIGH_FUEL else (2, 7)
        args = [rr.randint(lo, hi)] + [rr.randint(0, 9)] * (len(params) - 1)
        body = ["begin", ["print", [name] + args], body]
    parts.append(body)
    return parts


def _gen_func(g, idx):
    r = g.r
    name = "f%d" % idx
    fuel = g.fresh("k")
    acc = g.fresh("a")
    extra = []
    for _ in range(r.randint(0, 1)):
        extra.append(g.fresh("p"))
    params = [fuel, acc] + extra
    scope = set(params)
    base = _pick_base(g, S(acc), scope)
    if r.random() < 0.35:
        step_acc = ["*", S(acc), 2]          # geometric growth -> whistle bait
    else:
        step_acc = ["+", S(acc), r.randint(1, 5)]
    callargs = [["-", S(fuel), 1], step_acc] + \
        [_gen_small(g, scope | {fuel}) for _ in extra]
    rec = [name] + callargs
    alt = _gen_expr(g, [], scope=scope | {fuel}, fuel_var=fuel,
                    depth=2, budget=r.randint(4, 10))
    body = ["if", ["<=", fuel, 0], base,
            ["if", ["=", ["rem", fuel, r.choice([2, 3])], 0],
             rec, alt]]
    return (name, params, body)


def _pick_base(g, acc, scope):
    r = g.r
    c = r.randint(0, 3)
    if c == 0:
        return acc
    if c == 1:
        return ["+", acc, r.randint(-5, 5)]
    if c == 2:
        return r.randint(0, 20)
    return ["*", acc, 2]


def _gen_small(g, scope):
    r = g.r
    if not scope:
        return r.randint(0, 9)
    c = r.randint(0, 2)
    if c == 0:
        return r.randint(-9, 9)
    return S(r.choice(sorted(scope)))


def _gen_expr(g, funcs, scope, fuel_var, depth, budget):
    """budget counts remaining nodes; depth limits nesting."""
    r = g.r
    budget -= 1
    if budget <= 0:
        return _gen_atom(g, scope, funcs)
    choices = ["atom", "if", "let", "arith", "cmp", "list", "call"]
    if fuel_var is not None:
        pass  # recursion handled in func bodies only
    if depth < 7:
        choices += ["let", "arith", "box", "try", "begin", "list", "cmp"]
    if depth < 4:
        choices += ["lambda_app"]
    kind = r.choice(choices)
    if kind == "atom":
        return _gen_atom(g, scope, funcs)
    if kind == "if":
        return ["if",
                _gen_bool(g, scope, depth + 1),
                _gen_expr(g, funcs, scope, fuel_var, depth + 1, budget),
                _gen_expr(g, funcs, scope, fuel_var, depth + 1, budget)]
    if kind == "let":
        v = g.fresh("x")
        rhs = _gen_expr(g, funcs, scope, fuel_var, depth + 1,
                        max(1, budget // 2))
        bod = _gen_expr(g, funcs, scope | {v}, fuel_var, depth + 1,
                        max(1, budget // 2))
        return [["lambda", [v], bod], rhs]
        # note: v referenced only via scope in bod
    if kind == "arith":
        op = r.choice(["+", "-", "*", "min", "max"])
        return [op,
                _gen_int(g, scope, depth + 1),
                _gen_int(g, scope, depth + 1)]
    if kind == "cmp":
        op = r.choice(["<", ">", "<=", ">=", "="])
        return [op, _gen_int(g, scope, depth + 1), _gen_int(g, scope, depth + 1)]
    if kind == "list":
        n = r.randint(0, 3)
        xs = [_gen_small(g, scope) for _ in range(n)]
        out = []
        for x in reversed(xs):
            out = ["cons", x, out]
        return out
    if kind == "call" and funcs:
        name, params, _b = r.choice(funcs)
        args = [r.randint(0, 6)] + [_gen_small(g, scope) for _ in range(len(params) - 1)]
        return [name] + args
    if kind == "box":
        b = g.fresh("bx")
        init = _gen_int(g, scope, depth + 1)
        wval = _gen_int(g, scope | {b}, depth + 1)
        reads = _gen_expr(g, funcs, scope | {b}, fuel_var, depth + 1,
                          max(1, budget // 3))
        return [["lambda", [b],
                 ["begin",
                  ["set-box!", S(b), wval],
                  ["print", ["unbox", S(b)]],
                  reads]],
                ["box", init]]
    if kind == "try":
        pay = r.choice([r.randint(0, 9), ["quote", ("sym", "boom")]])
        handler_var = g.fresh("e")
        hv = S(handler_var)
        handler = ["lambda", [handler_var],
                   ["+", 1000,
                    ["if", ["pair?", hv],
                     ["car", ["cdr", hv]], 0]]]
        inner = _gen_expr(g, funcs, scope, fuel_var, depth + 1,
                          max(1, budget // 2))
        do_raise = r.random() < 0.35
        body = ["raise", pay] if do_raise else inner
        return ["try", body, handler]
    if kind == "begin":
        n = r.randint(2, 3)
        seqs = [_gen_stmt(g, funcs, scope, depth + 1) for _ in range(n - 1)]
        last = _gen_expr(g, funcs, scope, fuel_var, depth + 1, max(1, budget // 2))
        return ["begin"] + seqs + [last]
    if kind == "lambda_app":
        v = g.fresh("w")
        f = g.fresh("h")
        body = _gen_expr(g, funcs, scope | {f, v}, fuel_var, depth + 1,
                         max(1, budget // 2))
        arg = _gen_int(g, scope, depth + 1)
        return [["lambda", [f], [S(f), arg]],
                ["lambda", [v], ["+", S(v), 1]]]
    return _gen_atom(g, scope, funcs)


def _gen_stmt(g, funcs, scope, depth):
    r = g.r
    c = r.randint(0, 2)
    if c == 0:
        return ["print", _gen_small(g, scope)]
    if c == 1:
        return ["print", _gen_expr(g, funcs, scope, None, depth, 3)]
    return ["print", _gen_atom(g, scope, [])]


def _gen_int(g, scope, depth):
    r = g.r
    if scope and r.random() < 0.4:
        cand = sorted(scope)
        v = r.choice(cand)
        return S(v)
    if r.random() < 0.25 and depth < 4:
        op = r.choice(["+", "*", "-"])
        return [op, _gen_int(g, scope, depth + 1), r.randint(0, 7)]
    return r.randint(-9, 99)


def _gen_bool(g, scope, depth):
    r = g.r
    c = r.randint(0, 2)
    if c == 0:
        return r.choice([True, False])
    if c == 1:
        op = r.choice(["<", "<=", "=", ">", ">="])
        return [op, _gen_int(g, scope, depth), _gen_int(g, scope, depth)]
    return ["not", ["<", _gen_int(g, scope, depth), _gen_int(g, scope, depth)]]


def _gen_atom(g, scope, funcs):
    r = g.r
    c = r.randint(0, 3)
    if c < 2:
        return r.randint(-9, 42)
    if c == 2 and scope:
        return r.choice(sorted(scope))
    return r.choice([True, False, [], -3, 0])


def to_source(forms):
    from sc.sexp import pretty
    return "\n".join(pretty(f) for f in forms) + "\n"


# ---------------------------------------------------------------- comparing


def norm_value(v, depth=8):
    if isinstance(v, Pair):
        if depth <= 0:
            return "..."
        return ("p", norm_value(v.hd, depth - 1), norm_value(v.tl, depth - 1))
    if isinstance(v, Box):
        return "#box"
    if isinstance(v, Closure):
        return "#proc"
    if hasattr(v, "fid"):
        return "#proc"
    if v is None:
        return "()"
    if isinstance(v, bool) or isinstance(v, int):
        return v
    if isinstance(v, Sym):
        return ("sym", v.name)
    if isinstance(v, tuple) and len(v) == 2 and v[0] == "err":
        return v
    if isinstance(v, tuple):
        return ("?", str(v))
    return str(v)


def outcome_of(out_list, status, value):
    return (tuple(out_list), status, norm_value(value))


def compare(ref, base, opt):
    """ref/base/opt are vm/ref-interpreter outcome dicts."""
    r = outcome_of(ref["out"], ref["status"], ref["value"])
    b = outcome_of(base["out"], base["status"], base["value"])
    o = outcome_of(opt["out"], opt["status"], opt["value"])
    problems = []
    if r != b:
        problems.append(("ref-vs-base", r, b))
    if r != o:
        problems.append(("ref-vs-opt", r, o))
    if "writes" in ref and (ref.get("writes") != opt.get("writes")
                            or ref.get("writes") != base.get("writes")):
        problems.append(("mutation-trace", ref.get("writes"),
                         base.get("writes"), opt.get("writes")))
    return problems
