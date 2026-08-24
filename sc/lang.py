"""SC-Lang core AST + desugarer.

AST nodes are tagged tuples:
  ('const', value)            value: int | bool | None(nil) | str
  ('var', name)
  ('lam', [params], body)
  ('app', f, [args])
  ('if', c, t, e)
  ('let', [(n, e)], body)
  ('letrec', [(n, lam)], body)
  ('begin', [e])
  ('prim', name, [args])
  ('box', e) ('unbox', e) ('setbox', addr, val)
  ('try', body, handler)
  ('raise', e)

A Program is {'defs': [(name, lam)], 'body': expr}.
"""

PRIMS = {
    "+", "-", "*", "quot", "rem", "<", ">", "<=", ">=", "=",
    "abs", "min", "max", "not", "null?", "pair?", "eq?", "equal?",
    "cons", "car", "cdr", "print", "procedure?", "box?",
}

_ARITY = {
    "+": 2, "-": 2, "*": 2, "quot": 2, "rem": 2,
    "<": 2, ">": 2, "<=": 2, ">=": 2, "=": 2,
    "abs": 1, "min": 2, "max": 2, "not": 1,
    "null?": 1, "pair?": 1, "eq?": 2, "equal?": 2,
    "cons": 2, "car": 1, "cdr": 1, "print": 1,
    "procedure?": 1, "box?": 1,
}


class LangError(Exception):
    pass


_prim_param_counter = [0]


def _gensym_prim_param(i):
    _prim_param_counter[0] += 1
    return "pv%d" % _prim_param_counter[0]


def _sym(x):
    return isinstance(x, tuple) and x and x[0] == "sym"


def _name(x):
    return x[1] if _sym(x) else x


def desugar_top(forms) -> dict:
    """forms -> Program {'items': [...], 'body': expr}

    items is an ordered list preserving source order so closure conversion
    can place function-closure creation after preceding value definitions:
      ('def', name, lam)     -- lambda define
      ('val', name, expr)    -- non-lambda define
    """
    items = []
    body_forms = []
    for f in forms:
        if isinstance(f, list) and f and _name(f[0]) == "define":
            if isinstance(f[1], list):
                name2, lam = _desugar_define(f)
                items.append(("def", name2, lam))
            else:
                name = _name(f[1])
                rhs = f[2] if len(f) == 3 else None
                is_lambda = isinstance(rhs, list) and rhs and \
                    _name(rhs[0]) == "lambda"
                if is_lambda:
                    _, lam = _desugar_define(["define", name, rhs])
                    items.append(("def", name, lam))
                elif rhs is not None:
                    items.append(("val", name, desugar(rhs)))
                else:
                    raise LangError("bad define: %r" % (f,))
        elif isinstance(f, list) and f and _name(f[0]) == "declare":
            pass
        else:
            body_forms.append(f)
    if not body_forms:
        raise LangError("program has no top-level expression")
    body = desugar_begin(body_forms)
    return {"items": items, "body": body}


def _desugar_define(f):
    if len(f) < 3:
        raise LangError("bad define: %r" % (f,))
    target = f[1]
    if isinstance(target, list):  # (define (name . args) body...)
        fname = _name(target[0])
        params = [_name(p) for p in target[1:]]
        body = desugar_begin(f[2:])
        return fname, ("lam", params, body)
    name = _name(target)
    rest = f[2]
    rhs = desugar(rest)
    if not (isinstance(rhs, tuple) and rhs[0] == "lam"):
        raise LangError("define value must be lambda: %s" % name)
    return name, rhs


def desugar_begin(forms):
    forms = list(forms)
    if not forms:
        return ("const", None)
    if len(forms) == 1:
        return desugar(forms[0])
    return ("begin", [desugar(f) for f in forms])


def desugar(x):
    # atoms
    if isinstance(x, bool) or isinstance(x, int) or isinstance(x, str):
        return ("const", x)
    if _sym(x):
        n = x[1]
        if n == "nil":
            return ("const", None)
        if n in PRIMS:
            # primitive used as a value: eta-expand into a closure
            arity = _ARITY[n]
            params = ["%p%d" % (i,) for i in range(arity)] if False else \
                [_gensym_prim_param(i) for i in range(arity)]
            return ("lam", params,
                    ("prim", n, [("var", p) for p in params]))
        return ("var", n)
    if not isinstance(x, list):
        raise LangError("bad form %r" % (x,))
    if len(x) == 0:
        return ("const", None)

    head = x[0]

    if isinstance(head, list):
        # ((lambda ...) args) sugar
        f = desugar(head)
        return ("app", f, [desugar(a) for a in x[1:]])

    hname = _name(head)

    if hname == "quote":
        if len(x) != 2:
            raise LangError("bad quote")
        return _desugar_quote(x[1])
    if hname == "lambda":
        params = [_name(p) for p in x[1]]
        body = desugar_begin(x[2:])
        return ("lam", params, body)
    if hname == "if":
        if len(x) == 3:
            return ("if", desugar(x[1]), desugar(x[2]), ("const", None))
        if len(x) != 4:
            raise LangError("bad if")
        return ("if", desugar(x[1]), desugar(x[2]), desugar(x[3]))
    if hname == "begin":
        return desugar_begin(x[1:])
    if hname == "let":
        return _desugar_let(x)
    if hname == "let*":
        binds = [(_name(b[0]), desugar(b[1])) for b in x[1]]
        if not binds:
            return desugar_begin(x[2:])
        outer = binds[0]
        inner = ("let*", binds[1:], desugar_begin(x[2:]))
        return ("let", [outer], inner) if len(binds) > 0 else inner
    if hname == "letrec":
        binds = []
        for b in x[1]:
            rhs = desugar(b[1])
            if not (isinstance(rhs, tuple) and rhs[0] == "lam"):
                raise LangError("letrec values must be lambdas")
            binds.append((_name(b[0]), rhs))
        return ("letrec", binds, desugar_begin(x[2:]))
    if hname == "cond":
        return _desugar_cond(x[1:])
    if hname == "and":
        return _desugar_andor(x[1:], True)
    if hname == "or":
        return _desugar_andor(x[1:], False)
    if hname == "when":
        return ("if", desugar(x[1]), desugar_begin(x[2:]), ("const", None))
    if hname == "unless":
        return ("if", desugar(x[1]), ("const", None), desugar_begin(x[2:]))
    if hname == "list":
        return _desugar_list([desugar(a) for a in x[1:]])
    if hname == "set!":
        raise LangError("set! on variables unsupported; use boxes (set-box!)")
    if hname == "set-box!":
        if len(x) != 3:
            raise LangError("bad set-box!")
        return ("setbox", desugar(x[1]), desugar(x[2]))
    if hname == "box":
        return ("box", desugar(x[1]))
    if hname == "unbox":
        return ("unbox", desugar(x[1]))
    if hname == "raise":
        if len(x) != 2:
            raise LangError("bad raise")
        return ("raise", desugar(x[1]))
    if hname == "try":
        if len(x) != 3:
            raise LangError("bad try: (try body handler)")
        return ("try", desugar(x[1]), desugar(x[2]))
    if hname == "while":
        raise LangError("while unsupported; use recursion")

    if hname in PRIMS:
        want = _ARITY[hname]
        if len(x) - 1 != want:
            raise LangError("%s expects %d args, got %d" % (hname, want, len(x) - 1))
        return ("prim", hname, [desugar(a) for a in x[1:]])

    # application
    return ("app", desugar(head), [desugar(a) for a in x[1:]])


def _desugar_let(x):
    if len(x) < 3:
        raise LangError("bad let")
    if isinstance(x[1], tuple):
        # named let: (let loop ((v e)...) body...)
        loop = _name(x[1])
        binds = [(_name(b[0]), desugar(b[1])) for b in x[2]]
        params = [n for n, _ in binds]
        args = [e for _, e in binds]
        body = desugar_begin(x[3:])
        lam = ("lam", params, body)
        return ("letrec", [(loop, lam)], ("app", ("var", loop), args))
    if not isinstance(x[1], list):
        raise LangError("bad let bindings")
    binds = [(_name(b[0]), desugar(b[1])) for b in x[1]]
    return ("let", binds, desugar_begin(x[2:]))


def _desugar_quote(d):
    if d == []:
        return ("const", None)
    if isinstance(d, bool) or isinstance(d, int):
        return ("const", d)
    if _sym(d):
        from .semantics import Sym
        return ("const", Sym(d[1]))
    if isinstance(d, list):
        return _desugar_list([_desugar_quote(e) for e in d])
    raise LangError("bad quote datum")


def _desugar_list(args):
    acc = ("const", None)
    for a in reversed(args):
        acc = ("prim", "cons", [a, acc])
    return acc


def _desugar_cond(clauses):
    if not clauses:
        raise LangError("cond with no clauses")
    c = clauses[0]
    if isinstance(c[0], tuple) and c[0][0] == "sym" and c[0][1] == "else":
        if len(clauses) != 1:
            raise LangError("else must be last cond clause")
        return desugar_begin(c[1:])
    test = desugar(c[0])
    if len(clauses) == 1:
        tail = ("const", None)
    else:
        tail = _desugar_cond(clauses[1:])
    body = desugar_begin(c[1:]) if len(c) > 1 else test
    return ("if", test, body, tail)


def _desugar_andor(args, is_and):
    if not args:
        return ("const", is_and)
    if len(args) == 1:
        return desugar(args[0])
    first = desugar(args[0])
    rest = _desugar_andor(args[1:], is_and)
    if is_and:
        return ("if", first, rest, ("const", False))
    return ("if", first, ("const", True), rest)


def free_vars(e, bound=frozenset()):
    """Set of free variable names."""
    tag = e[0]
    if tag == "const":
        return set()
    if tag == "var":
        return {e[1]} - set(bound)
    if tag == "lam":
        return free_vars(e[2], bound | set(e[1]))
    if tag == "app":
        return free_vars(e[1], bound) | {v for a in e[2] for v in free_vars(a, bound)}
    if tag == "if":
        return free_vars(e[1], bound) | free_vars(e[2], bound) | free_vars(e[3], bound)
    if tag == "let":
        fv = set()
        for _, rhs in e[1]:
            fv |= free_vars(rhs, bound)
        nb = bound | {n for n, _ in e[1]}
        return fv | free_vars(e[2], nb)
    if tag == "letrec":
        nb = bound | {n for n, _ in e[1]}
        fv = set()
        for _, lam in e[1]:
            fv |= free_vars(lam, nb)
        return fv | free_vars(e[2], nb)
    if tag == "begin":
        return {v for x in e[1] for v in free_vars(x, bound)}
    if tag == "prim":
        return {v for a in e[2] for v in free_vars(a, bound)}
    if tag == "box":
        return free_vars(e[1], bound)
    if tag == "unbox":
        return free_vars(e[1], bound)
    if tag == "setbox":
        return free_vars(e[1], bound) | free_vars(e[2], bound)
    if tag == "try":
        return free_vars(e[1], bound) | free_vars(e[2], bound)
    if tag == "raise":
        return free_vars(e[1], bound)
    raise LangError("free_vars: bad node %r" % (tag,))


def size_of(e):
    tag = e[0]
    if tag in ("const", "var"):
        return 1
    if tag == "lam":
        return 1 + size_of(e[2])
    if tag == "app":
        return 1 + size_of(e[1]) + sum(size_of(a) for a in e[2])
    if tag == "if":
        return 1 + size_of(e[1]) + size_of(e[2]) + size_of(e[3])
    if tag == "let":
        return sum(1 + size_of(rhs) for _, rhs in e[1]) + size_of(e[2])
    if tag == "letrec":
        return sum(size_of(lam) for _, lam in e[1]) + size_of(e[2])
    if tag == "begin":
        return sum(size_of(x) for x in e[1])
    if tag == "prim":
        return 1 + sum(size_of(a) for a in e[2])
    if tag in ("box", "unbox", "raise"):
        return 1 + size_of(e[1])
    if tag == "setbox":
        return 1 + size_of(e[1]) + size_of(e[2])
    if tag == "try":
        return 1 + size_of(e[1]) + size_of(e[2])
    raise LangError("size_of: bad node %r" % (tag,))
