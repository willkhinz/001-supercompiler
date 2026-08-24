"""Shared value semantics: data types, primitives, printing, equality.

Used by BOTH the reference interpreter and the bytecode VM so that primitive
behavior (including error identities and formatting) cannot drift apart.
Control flow, environments, and exception plumbing remain independent.
"""
from __future__ import annotations


class Sym:
    __slots__ = ("name",)
    _table = {}

    def __new__(cls, name):
        s = cls._table.get(name)
        if s is None:
            s = object.__new__(cls)
            s.name = name
            cls._table[name] = s
        return s

    def __repr__(self):
        return self.name


class Pair:
    __slots__ = ("hd", "tl")

    def __init__(self, hd, tl):
        self.hd = hd
        self.tl = tl


class Box:
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v


class Closure:
    """Closure used by the reference interpreter."""
    __slots__ = ("params", "body", "env")

    def __init__(self, params, body, env):
        self.params = params
        self.body = body
        self.env = env


class ScmError(Exception):
    def __init__(self, msg):
        super().__init__(msg)
        self.msg = msg


class ScmRaise(Exception):
    def __init__(self, payload):
        self.payload = payload


ERR_INT_OP = "err:non-int-operand"
ERR_DIV0 = "err:division-by-zero"
ERR_CAR = "err:car-of-non-pair"
ERR_CDR = "err:cdr-of-non-pair"
ERR_NOTBOOL = "err:if-condition-not-bool"
ERR_NOTPROC = "err:call-of-non-closure"
ERR_NOTBOX = "err:box-op-on-non-box"
ERR_ARITY = "err:bad-arity"
ERR_NOTPAIR_PRED = None  # unused

PURE_PRIMS = {
    "+", "-", "*", "quot", "rem", "<", ">", "<=", ">=", "=",
    "abs", "min", "max", "not", "null?", "pair?", "eq?", "equal?",
    "cons", "car", "cdr", "procedure?", "box?",
}
EFFECT_PRIMS = {"print", "set-box!"}
DYNAMIC_PRIMS = {"unbox"}          # depends on mutable cell: never static
ALL_PRIMS = PURE_PRIMS | EFFECT_PRIMS | DYNAMIC_PRIMS


def _int(v):
    if isinstance(v, bool) or not isinstance(v, int):
        raise ScmError(ERR_INT_OP)
    return v


def prim(name, args):
    """Apply primitive. Raises ScmError on runtime faults."""
    if name == "+":
        return _int(args[0]) + _int(args[1])
    if name == "-":
        return _int(args[0]) - _int(args[1])
    if name == "*":
        return _int(args[0]) * _int(args[1])
    if name == "quot":
        a, b = _int(args[0]), _int(args[1])
        if b == 0:
            raise ScmError(ERR_DIV0)
        q = abs(a) // abs(b)
        return q if (a >= 0) == (b >= 0) else -q
    if name == "rem":
        a, b = _int(args[0]), _int(args[1])
        if b == 0:
            raise ScmError(ERR_DIV0)
        q = abs(a) // abs(b)
        q = q if (a >= 0) == (b >= 0) else -q
        return a - b * q
    if name in ("<", ">", "<=", ">=", "="):
        a, b = _int(args[0]), _int(args[1])
        if name == "<":
            return a < b
        if name == ">":
            return a > b
        if name == "<=":
            return a <= b
        if name == ">=":
            return a >= b
        return a == b
    if name == "abs":
        return abs(_int(args[0]))
    if name in ("min", "max"):
        a, b = _int(args[0]), _int(args[1])
        return min(a, b) if name == "min" else max(a, b)
    if name == "not":
        v = args[0]
        if not isinstance(v, bool):
            raise ScmError("err:not-of-non-bool")
        return not v
    if name == "null?":
        return args[0] is None
    if name == "pair?":
        return isinstance(args[0], Pair)
    if name == "procedure?":
        return isinstance(args[0], (Closure,)) or hasattr(args[0], "fid")
    if name == "box?":
        return isinstance(args[0], Box)
    if name == "eq?":
        a, b = args
        if isinstance(a, int) and not isinstance(a, bool):
            return isinstance(b, int) and not isinstance(b, bool) and a == b
        if isinstance(a, Sym):
            return a is b
        return a is b
    if name == "equal?":
        return scm_equal(args[0], args[1])
    if name == "cons":
        return Pair(args[0], args[1])
    if name == "car":
        if not isinstance(args[0], Pair):
            raise ScmError(ERR_CAR)
        return args[0].hd
    if name == "cdr":
        if not isinstance(args[0], Pair):
            raise ScmError(ERR_CDR)
        return args[0].tl
    if name == "print":
        raise RuntimeError("print handled by executor")
    if name == "set-box!":
        b = args[0]
        if not isinstance(b, Box):
            raise ScmError(ERR_NOTBOX)
        b.v = args[1]
        return None
    if name == "unbox":
        b = args[0]
        if not isinstance(b, Box):
            raise ScmError(ERR_NOTBOX)
        return b.v
    raise AssertionError("unknown prim %s" % name)


def format_value(v, depth=6):
    if isinstance(v, Sym):
        return v.name
    if v is None:
        return "()"
    if v is True:
        return "#t"
    if v is False:
        return "#f"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return '"%s"' % v
    if isinstance(v, Pair):
        if depth <= 0:
            return "(...)"
        items = []
        cur = v
        while isinstance(cur, Pair):
            items.append(format_value(cur.hd, depth - 1))
            cur = cur.tl
        if cur is None:
            return "(" + " ".join(items) + ")"
        return "(" + " ".join(items) + " . " + format_value(cur, depth - 1) + ")"
    if isinstance(v, Closure):
        return "#<procedure>"
    if hasattr(v, "fid"):
        return "#<procedure>"
    if isinstance(v, Box):
        return "#<box>"
    return str(v)


def scm_equal(a, b, depth=50):
    if depth <= 0:
        return a is b
    if isinstance(a, bool) or isinstance(b, bool):
        return a is b
    if isinstance(a, int) and isinstance(b, int):
        return a == b
    if isinstance(a, Sym) and isinstance(b, Sym):
        return a.name == b.name
    if a is None or b is None:
        return a is b
    if isinstance(a, Pair) and isinstance(b, Pair):
        return scm_equal(a.hd, b.hd, depth - 1) and scm_equal(a.tl, b.tl, depth - 1)
    return a is b
