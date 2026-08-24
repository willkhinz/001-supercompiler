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
    steps = [0]

    def _eval(e, env):
        return eval_expr(e, env, out, steps, fuel)

    try:
        env = {}
        for name, lam in prog["defs"]:
            env[name] = Closure(lam[1], lam[2], env)
        val = eval_expr(prog["body"], env, out, steps, fuel)
        status, res = "ok", val
    except ScmRaise as r:
        status, res = "exc", r.payload
    except ScmError as e:
        status, res = "exc", ("err", e.msg)
    except RecursionError:
        status, res = "timeout", None
    return {"out": out, "status": status, "value": res}


def eval_expr(e, env, out, steps, fuel):
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
        args = [eval_expr(a, env, out, steps, fuel) for a in e[2]]
        if name == "print":
            out.append(format_value(args[0]))
            return None
        return prim(name, args)
    if tag == "app":
        f = eval_expr(e[1], env, out, steps, fuel)
        args = [eval_expr(a, env, out, steps, fuel) for a in e[2]]
        return apply_closure(f, args, out, steps, fuel)
    if tag == "if":
        c = eval_expr(e[1], env, out, steps, fuel)
        if not isinstance(c, bool):
            raise ScmError("err:if-condition-not-bool")
        return eval_expr(e[2] if c else e[3], env, out, steps, fuel)
    if tag == "let":
        new = dict(env)
        for n, rhs in e[1]:
            new[n] = eval_expr(rhs, new, out, steps, fuel)
        return eval_expr(e[2], new, out, steps, fuel)
    if tag == "letrec":
        new = dict(env)
        for n, lam in e[1]:
            new[n] = Closure(lam[1], lam[2], new)
        return eval_expr(e[2], new, out, steps, fuel)
    if tag == "begin":
        v = None
        for x in e[1]:
            v = eval_expr(x, env, out, steps, fuel)
        return v
    if tag == "box":
        return Box(eval_expr(e[1], env, out, steps, fuel))
    if tag == "unbox":
        b = eval_expr(e[1], env, out, steps, fuel)
        if not isinstance(b, Box):
            raise ScmError("err:box-op-on-non-box")
        return b.v
    if tag == "setbox":
        b = eval_expr(e[1], env, out, steps, fuel)
        v = eval_expr(e[2], env, out, steps, fuel)
        if not isinstance(b, Box):
            raise ScmError("err:box-op-on-non-box")
        b.v = v
        return None
    if tag == "raise":
        raise ScmRaise(eval_expr(e[1], env, out, steps, fuel))
    if tag == "try":
        try:
            return eval_expr(e[1], env, out, steps, fuel)
        except ScmRaise as r:
            h = eval_expr(e[2], env, out, steps, fuel)
            return apply_closure(h, [r.payload], out, steps, fuel)
        except ScmError as se:
            h = eval_expr(e[2], env, out, steps, fuel)
            return apply_closure(h, [("err", se.msg)], out, steps, fuel)
    if tag == "mkclo":
        raise LangError("mkclo reached refinterp")
    raise LangError("refinterp: bad node %r" % (tag,))


def apply_closure(f, args, out, steps, fuel):
    if not isinstance(f, Closure):
        raise ScmError("err:call-of-non-closure")
    if len(args) != len(f.params):
        raise ScmError("err:bad-arity")
    call_env = dict(f.env or {})
    call_env.update(zip(f.params, args))
    return eval_expr(f.body, call_env, out, steps, fuel)
