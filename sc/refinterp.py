"""Reference interpreter (independent oracle): tree-walking evaluation on the
desugared AST. Shares only value semantics from sc.semantics.
"""
from __future__ import annotations

from .lang import LangError
from .semantics import (
    Box, Closure, Pair, ScmError, ScmRaise, format_value, prim,
)


def run_program(prog: dict, fuel=50_000_000):
    """prog: desugared Program dict -> Outcome dict."""
    out = []
    writes = []
    steps = [0]

    def _eval(e, env):
        return eval_expr(e, env, out, writes, steps, fuel)

    try:
        env = {}
        for item in prog.get("items", []):
            if item[0] == "def":
                _, name, lam = item
                env[name] = Closure(lam[1], lam[2], env)
            elif item[0] == "val":
                _, name, rhs = item
                env[name] = eval_expr(rhs, env, out, writes, steps, fuel)
        val = eval_expr(prog["body"], env, out, writes, steps, fuel)
        status, res = "ok", val
    except ScmRaise as r:
        status, res = "exc", r.payload
    except ScmError as e:
        status, res = "exc", ("err", e.msg)
    except RecursionError:
        status, res = "timeout", None
    return {"out": out, "status": status, "value": res, "writes": writes}


def _norm_write_ref(v):
    from .semantics import Sym
    if isinstance(v, bool) or isinstance(v, int):
        return v
    if v is None:
        return "()"
    if isinstance(v, Sym):
        return ("sym", v.name)
    return "#obj"


def eval_expr(e, env, out, writes, steps, fuel):
    steps[0] += 1
    if steps[0] > fuel:
        raise RecursionError()
    tag = e[0]
    if tag == "const":
        return e[1]
    if tag == "var":
        try:
            return env[e[1]]
        except KeyError:
            raise ScmError("err:unbound:" + e[1])
    if tag == "lam":
        return Closure(e[1], e[2], env)
    if tag == "prim":
        name = e[1]
        args = [eval_expr(a, env, out, writes, steps, fuel) for a in e[2]]
        if name == "print":
            out.append(format_value(args[0]))
            return None
        return prim(name, args)
    if tag == "app":
        f = eval_expr(e[1], env, out, writes, steps, fuel)
        args = [eval_expr(a, env, out, writes, steps, fuel) for a in e[2]]
        return apply_closure(f, args, out, writes, steps, fuel)
    if tag == "if":
        c = eval_expr(e[1], env, out, writes, steps, fuel)
        if not isinstance(c, bool):
            raise ScmError("err:if-condition-not-bool")
        return eval_expr(e[2] if c else e[3], env, out, writes, steps, fuel)
    if tag == "let":
        new = dict(env)
        for n, rhs in e[1]:
            new[n] = eval_expr(rhs, new, out, writes, steps, fuel)
        return eval_expr(e[2], new, out, writes, steps, fuel)
    if tag == "letrec":
        new = dict(env)
        for n, lam in e[1]:
            new[n] = Closure(lam[1], lam[2], new)
        return eval_expr(e[2], new, out, writes, steps, fuel)
    if tag == "begin":
        v = None
        for x in e[1]:
            v = eval_expr(x, env, out, writes, steps, fuel)
        return v
    if tag == "box":
        return Box(eval_expr(e[1], env, out, writes, steps, fuel))
    if tag == "unbox":
        b = eval_expr(e[1], env, out, writes, steps, fuel)
        if not isinstance(b, Box):
            raise ScmError("err:box-op-on-non-box")
        return b.v
    if tag == "setbox":
        b = eval_expr(e[1], env, out, writes, steps, fuel)
        v = eval_expr(e[2], env, out, writes, steps, fuel)
        if not isinstance(b, Box):
            raise ScmError("err:box-op-on-non-box")
        b.v = v
        writes.append(_norm_write_ref(v))
        return None
    if tag == "raise":
        raise ScmRaise(eval_expr(e[1], env, out, writes, steps, fuel))
    if tag == "try":
        try:
            return eval_expr(e[1], env, out, writes, steps, fuel)
        except ScmRaise as r:
            h = eval_expr(e[2], env, out, writes, steps, fuel)
            return apply_closure(h, [r.payload], out, writes, steps, fuel)
        except ScmError as se:
            h = eval_expr(e[2], env, out, writes, steps, fuel)
            return apply_closure(h, [("err", se.msg)], out, writes, steps, fuel)
    if tag == "mkclo":
        raise LangError("mkclo reached refinterp")
    raise LangError("refinterp: bad node %r" % (tag,))


def apply_closure(f, args, out, writes, steps, fuel):
    if not isinstance(f, Closure):
        raise ScmError("err:call-of-non-closure")
    if len(args) != len(f.params):
        raise ScmError("err:bad-arity")
    call_env = dict(f.env or {})
    call_env.update(zip(f.params, args))
    return eval_expr(f.body, call_env, out, writes, steps, fuel)
