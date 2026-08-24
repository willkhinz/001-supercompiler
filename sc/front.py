"""Front end: closure conversion (lambda lifting) + ANF normalization.

Output shapes
-------------
Lifted program : {'funds': {fid: (params, body)}, 'main': expr}
   body exprs use nodes: const/var/app/prim/if/let/begin/box/unbox/
   setbox/try/raise/mkclo(fid,[exprs])

ANF program    : {'funds': {fid: (params, term)}, 'main': term}
   atoms  : ('acon', v) | ('avar', n)
   terms  :
     ('ahalt', a)
     ('araise', a)
     ('alet', name, rhs, body)
        rhs: ('aprim', p, [a])       p in PRIMS (incl 'set-box!')
             ('aapp', fatom, [a])
             ('amkclo', fid, [a])
             ('abox', a) ('aunbox', a) ('asetbox', a1, a2)
     ('aif', c, t, e)
     ('atry', name, body_term, handler_atom, cont_term)

All binders are globally unique (alpha-renamed here).
"""
from __future__ import annotations

from .lang import LangError, free_vars

# ---------------------------------------------------------------- naming


class Namer:
    def __init__(self):
        self.n = 0

    def fresh(self, base="%"):
        self.n += 1
        return "%s%d" % (base, self.n)


# ---------------------------------------------------- closure conversion


def closure_convert(prog: dict) -> dict:
    """Lambda lifting with correct mutual recursion.

    Function-ish names (top-level defines and letrec binders) are resolved to
    ('mkclo', fid, [free-var exprs]) at every reference site, so closures are
    stateless w.r.t. the function table and recursion works by construction.
    """
    namer = Namer()
    funds: dict = {}
    top_names = {name for name, _ in prog["defs"]}
    # name -> (fid, [freevar names]); active letrec scope stack entries
    fn_map_stack = []

    def lookup_fn(name):
        for m in reversed(fn_map_stack):
            if name in m:
                return m[name]
        return None

    def go(e):
        tag = e[0]
        if tag == "const":
            return e
        if tag == "var":
            fn = lookup_fn(e[1])
            if fn is not None:
                fid, fvs = fn
                return ("mkclo", fid, [("var", v) for v in fvs])
            if e[1] in top_names:
                return ("mkclo", e[1], [])
            return e
        if tag == "lam":
            return _lift(e)
        if tag == "app":
            return ("app", go(e[1]), [go(a) for a in e[2]])
        if tag == "prim":
            return ("prim", e[1], [go(a) for a in e[2]])
        if tag == "if":
            return ("if", go(e[1]), go(e[2]), go(e[3]))
        if tag == "let":
            binds = []
            ren = {}
            for n, rhs in e[1]:
                nn = namer.fresh(n[:8] + ".")
                ren[n] = nn
                binds.append((nn, go(rhs)))
            return ("let", binds, go(rename_go(e[2], ren)))
        if tag == "letrec":
            ren = {}
            names = []
            entries = {}
            lams = []
            for n, lam in e[1]:
                nn = namer.fresh(n[:8] + ".")
                ren[n] = nn
                names.append(nn)
                lams.append(lam)
            orig_names = {n for n, _ in e[1]}
            ext_tops = set(names) | orig_names | top_names
            for nn, lam in zip(names, lams):
                params, body = lam[1], lam[2]
                rp = {}
                nparams = []
                for p in params:
                    np_ = namer.fresh(p[:6] + ".")
                    rp[p] = np_
                    nparams.append(np_)
                rbody = rename_go(body, rp)
                fv = sorted(v for v in (free_vars(rbody) - set(nparams))
                            if v not in ext_tops)
                fid = namer.fresh("$f")
                entries[nn] = (fid, fv)
            return _letrec_simple(e, ren, names, entries, lams, ext_tops)
        if tag == "begin":
            return ("begin", [go(x) for x in e[1]])
        if tag == "box":
            return ("box", go(e[1]))
        if tag == "unbox":
            return ("unbox", go(e[1]))
        if tag == "setbox":
            return ("setbox", go(e[1]), go(e[2]))
        if tag == "try":
            return ("try", go(e[1]), go(e[2]))
        if tag == "raise":
            return ("raise", go(e[1]))
        if tag == "mkclo":
            return ("mkclo", e[1], [go(a) for a in e[2]])
        raise LangError("cc: bad node %r" % (tag,))

    def _letrec_simple(e, ren, names, entries, lams, ext_tops):
        fn_map_stack.append(entries)
        try:
            binds = []
            for nn, lam in zip(names, lams):
                fid, fv = entries[nn]
                node = _lift(rename_go(lam, ren))
                # _lift created its own fund; move it under our fid
                inner_fid = node[1]
                params, body = funds.pop(inner_fid)
                funds[fid] = (fv + params, body)
                binds.append((nn, ("mkclo", fid, [("var", v) for v in fv])))
            body = go(rename_go(e[2], ren))
        finally:
            fn_map_stack.pop()
        return ("let", binds, body)

    def _lift(e, extra_ren=None, skip_fv=frozenset()):
        """Lift one lambda into funds; returns ('mkclo', fid, [var exprs])."""
        params, body = e[1], e[2]
        ren = {}
        nparams = []
        for p in params:
            np_ = namer.fresh(p[:6] + ".")
            ren[p] = np_
            nparams.append(np_)
        nbody = rename_go(body, ren)
        fv = sorted(v for v in (free_vars(nbody) - set(nparams))
                    if v not in top_names and v not in skip_fv
                    and lookup_fn(v) is None)
        lifted_body = go(nbody)
        fid = namer.fresh("$f")
        funds[fid] = (fv + nparams, lifted_body)
        return ("mkclo", fid, [("var", v) for v in fv])

    def rename_go(e, ren):
        if not ren:
            return e
        tag = e[0]
        if tag == "const":
            return e
        if tag == "var":
            return ("var", ren.get(e[1], e[1]))
        if tag == "lam":
            nb = {k: v for k, v in ren.items() if k not in set(e[1])}
            return ("lam", e[1], rename_go(e[2], nb))
        if tag == "app":
            return ("app", rename_go(e[1], ren), [rename_go(a, ren) for a in e[2]])
        if tag == "prim":
            return ("prim", e[1], [rename_go(a, ren) for a in e[2]])
        if tag == "if":
            return ("if", rename_go(e[1], ren), rename_go(e[2], ren),
                    rename_go(e[3], ren))
        if tag == "let":
            binds = [(n, rename_go(rhs, _hide(ren, n))) for n, rhs in e[1]]
            return ("let", binds, rename_go(e[2], _hide_all(ren, {n for n, _ in e[1]})))
        if tag == "letrec":
            hidden = {n for n, _ in e[1]}
            binds = [(n, rename_go(lam, _hide(ren, n))) for n, lam in e[1]]
            return ("letrec", binds, rename_go(e[2], _hide_all(ren, hidden)))
        if tag == "begin":
            return ("begin", [rename_go(x, ren) for x in e[1]])
        if tag == "box":
            return ("box", rename_go(e[1], ren))
        if tag == "unbox":
            return ("unbox", rename_go(e[1], ren))
        if tag == "setbox":
            return ("setbox", rename_go(e[1], ren), rename_go(e[2], ren))
        if tag == "try":
            return ("try", rename_go(e[1], ren), rename_go(e[2], ren))
        if tag == "raise":
            return ("raise", rename_go(e[1], ren))
        if tag == "mkclo":
            return ("mkclo", e[1], [rename_go(a, ren) for a in e[2]])
        raise LangError("rename: bad node %r" % (tag,))

    def _hide(ren, n):
        nb = dict(ren)
        nb.pop(n, None)
        return nb

    def _hide_all(ren, names):
        return {k: v for k, v in ren.items() if k not in names}

    # ---- top-level defs
    out_funds = {}
    prologue = []
    for name, lam in prog["defs"]:
        node = _lift(lam)
        assert node[0] == "mkclo"
        fid = node[1]
        out_funds[name] = funds.pop(fid)
        prologue.append((name, ("mkclo", name, [])))

    main = prog["body"]
    for name, mk in reversed(prologue):
        main = ("let", [(name, mk)], main)
    main = go(main)

    out_funds.update(funds)
    return {"funds": out_funds, "main": main}

# ------------------------------------------------------------------ ANF


class Anfer:
    def __init__(self):
        self.namer = Namer()

    def convert(self, lifted: dict) -> dict:
        funds = {}
        for fid, (params, body) in lifted["funds"].items():
            funds[fid] = (params, self.term(body, lambda a: ("ahalt", a)))
        main = self.term(lifted["main"], lambda a: ("ahalt", a))
        return {"funds": funds, "main": main}

    # ---- helpers

    def atom(self, e, k):
        """Normalize e to an atom, then continue."""
        tag = e[0]
        if tag == "const":
            return k(("acon", e[1]))
        if tag == "var":
            return k(("avar", e[1]))
        if tag == "lam":
            raise LangError("bare lambda after cc")
        if tag in ("if", "begin", "try", "raise", "let", "letrec"):
            # non-atomic control form in operand position: normalize as a
            # term whose branches all continue with k
            return self.term(e, k)

        t = self.fresh_t()

        def kont(_):
            return k(("avar", t))

        return self.rhs_bind(t, e, kont)

    def fresh_t(self):
        return self.namer.fresh("t")

    def rhs_bind(self, name, e, k):
        """Bind `name` to the value of non-atomic e, then continue."""
        tag = e[0]
        if tag == "app":
            return self.atom(e[1], lambda fa: self.atoms(e[2], lambda fas: (
                ("alet", name, ("aapp", fa, fas), k(None)))))
        if tag == "prim":
            return self.atoms(e[2], lambda as_: (("alet", name, ("aprim", e[1], as_), k(None))))
        if tag == "mkclo":
            return self.atoms(e[2], lambda as_: (("alet", name, ("amkclo", e[1], as_), k(None))))
        if tag == "box":
            return self.atom(e[1], lambda a: (("alet", name, ("abox", a), k(None))))
        if tag == "unbox":
            return self.atom(e[1], lambda a: (("alet", name, ("aunbox", a), k(None))))
        if tag == "setbox":
            return (self.atom(e[1], lambda a1: self.atom(e[2], lambda a2: (
                ("alet", name, ("aprim", "set-box!", [a1, a2]), k(None))))))
        raise LangError("rhs_bind: %r" % (tag,))

    def atoms(self, es, k):
        def rec(i, vals):
            if i == len(es):
                return k(vals)
            return self.atom(es[i], lambda a: rec(i + 1, vals + [a]))
        return rec(0, [])

    def term(self, e, k):
        """Normalize e as a term (tail position), continuing with atom->term."""
        tag = e[0]
        if tag in ("const", "var", "app", "prim", "mkclo", "box", "unbox", "setbox"):
            return self.atom(e, k)
        if tag == "lam":
            raise LangError("bare lambda in term pos")
        if tag == "if":
            return self.atom(e[1], lambda c: (
                ("aif", c, self.term(e[2], k), self.term(e[3], k))))
        if tag == "let":
            def rec(i):
                if i == len(e[1]):
                    return self.term(e[2], k)
                n, rhs = e[1][i]

                def kk(_):
                    return rec(i + 1)
                if isinstance(rhs, tuple) and rhs[0] in ("const", "var"):
                    # substitute constant/var directly? keep binding for uniformity
                    pass
                return self.rhs_bind_named(n, rhs, kk)
            return rec(0)
        if tag == "letrec":
            raise LangError("letrec survived cc")
        if tag == "begin":
            def rec(i):
                if i == len(e[1]) - 1:
                    return self.term(e[1][i], k)
                return self.term(e[1][i], lambda _a: rec(i + 1))
            if not e[1]:
                return k(("acon", None))
            return rec(0)
        if tag == "try":
            nm = self.fresh_t()
            return self.atom(e[2], lambda ha: (
                ("atry", nm, self.term(e[1], lambda a: ("ahalt", a)), ha,
                 k(("avar", nm)))))
        if tag == "raise":
            return self.atom(e[1], lambda a: ("araise", a))
        raise LangError("anf.term: bad node %r" % (tag,))

    def rhs_bind_named(self, name, rhs, k):
        """Like rhs_bind but keeps the source name (already unique from cc)."""
        tag = rhs[0]
        if tag in ("const", "var"):
            a = ("acon", rhs[1]) if tag == "const" else ("avar", rhs[1])
            return (("alet", name, ("acopy", a), k(None)))
        return self.rhs_bind(name, rhs, k)
