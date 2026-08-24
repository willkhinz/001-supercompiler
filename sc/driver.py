"""The supercompiler: driving, whistle (homeomorphic embedding),
generalization, folding.

Soundness rules implemented here (full statements in README):

  E1  Boxes are opaque: box/unbox/set-box! always residualized, in ANF
      order, never cached or eliminated.
  E2  Pairs are immutable: cons may be computed into symbolic constructor
      terms; car/cdr deconstruct purely.
  E3  Effectful primitives (print, set-box!) are never evaluated
      statically; emitted exactly once, in ANF order.
  E4  Branch pruning only on statically-known boolean conditions;
      otherwise both branches are driven and joined residually.
  E5  A static value result implies its effects were already emitted.
  E6  Static exception propagation only rewrites a definite `raise v`
      into its lexically enclosing *driven* try; residual raises are
      caught by residual tries at runtime.
"""
from __future__ import annotations

from . import he as HE
from .semantics import PURE_PRIMS, ScmError, prim as apply_prim

FAIL = object()

_RRHS = {"aprim", "rprim", "aapp", "rcall", "adirect", "amkclo",
         "abox", "runbox", "abox2", "aunbox", "asetbox", "acopy", "rcopy",
         "rsub", "rifv", "rtry", "rexp"}


class Bail(Exception):
    pass


# ------------------------------------------------------------------ values

def is_scalar(v):
    return not isinstance(v, tuple)


def is_dyn(v):
    return isinstance(v, tuple) and v and v[0] == "dyn"


def is_case(v):
    return isinstance(v, tuple) and v and v[0] == "case"


def val_eq(a, b):
    if is_scalar(a) or is_scalar(b):
        if isinstance(a, bool) != isinstance(b, bool):
            return False
        try:
            return bool(a == b)
        except Exception:
            return a is b
    if a[0] != b[0]:
        return False
    k = a[0]
    if k == "dyn":
        return a[1] == b[1]
    if k == "sclo":
        return a[1] == b[1] and len(a[2]) == len(b[2]) and \
            all(val_eq(x, y) for x, y in zip(a[2], b[2]))
    if k == "scons":
        return val_eq(a[1], b[1]) and val_eq(a[2], b[2])
    if k == "case":
        return a[1] == b[1] and val_eq(a[2], b[2]) and val_eq(a[3], b[3])
    return False


def context_free(v):
    """True iff the value carries no driver-context names, so it may be used
    literally inside a freshly created residual function."""
    if is_scalar(v):
        return True
    if v[0] == "sclo":
        return all(context_free(x) for x in v[2])
    if v[0] == "scons":
        return context_free(v[1]) and context_free(v[2])
    return False


def valtree(v, depth=0):
    if depth > 60:
        return ("#deep",)
    if isinstance(v, bool):
        return ("b", v)
    if isinstance(v, int):
        return ("i", v)
    if v is None:
        return ("nil",)
    if is_scalar(v):
        if isinstance(v, tuple):
            return ("e", str(v[1]))
        return ("s", v.name)
    k = v[0]
    if k == "dyn":
        return ("D",)
    if k == "sclo":
        return ("#clo", v[1], tuple(valtree(x, depth + 1) for x in v[2]))
    if k == "scons":
        return ("#cons", valtree(v[1], depth + 1), valtree(v[2], depth + 1))
    if k == "case":
        c = v[1]
        ct = ("D",) if c[0] == "rvar" else valtree(c[1], depth + 1)
        return ("#case", ct, valtree(v[2], depth + 1), valtree(v[3], depth + 1))
    raise AssertionError("valtree %r" % (v,))


def freeze_val(v, depth=0):
    if depth > 30:
        return "#"
    if isinstance(v, bool):
        return "b%d" % v
    if isinstance(v, int):
        return "i%d" % v
    if v is None:
        return "n"
    if is_scalar(v):
        if isinstance(v, tuple):
            return "e" + str(v[1])
        return "s" + v.name
    k = v[0]
    if k == "dyn":
        return "D"
    if k == "sclo":
        return "(c %s %s)" % (v[1], " ".join(freeze_val(x, depth + 1)
                                             for x in v[2]))
    if k == "scons":
        return "(%s %s)" % (freeze_val(v[1], depth + 1),
                            freeze_val(v[2], depth + 1))
    return "{CASE}"


# ---------------------------------------------------------------- options

class Options:
    def __init__(self, **kw):
        self.specialize = kw.get("specialize", True)
        self.expand_factor = kw.get("expand_factor", 16.0)
        self.max_history = kw.get("max_history", 60)
        self.max_funcs = kw.get("max_funcs", 4000)
        self.max_cfg_depth = kw.get("max_cfg_depth", 6000)
        self.min_repeat = kw.get("min_repeat", 2)
        self.no_specialize = set(kw.get("no_specialize", ()))
        self.per_func_budget = dict(kw.get("per_func_budget", {}))


class Cfg:
    __slots__ = ("fid", "tree", "slots", "names")

    def __init__(self, fid, tree, slots, names):
        self.fid = fid
        self.tree = tree
        self.slots = slots
        self.names = names

    def as_tree(self):
        sl = []
        for s in self.slots:
            if is_dyn(s) or is_case(s):
                sl.append(("D",))
            else:
                sl.append(valtree(s))
        return ("#cfg", self.tree, ("#slots", *sl))


class FoldEntry:
    __slots__ = ("gname", "fid", "fixed", "params", "nslots")

    def __init__(self, gname, fid, fixed, params, nslots):
        self.gname = gname
        self.fid = fid
        self.fixed = fixed
        self.params = params
        self.nslots = nslots


# ================================================================= driver

class Driver:
    def __init__(self, anfprog, opts=None):
        self.anf = anfprog
        self.funds = anfprog["funds"]
        self.opts = opts or Options()
        self.res_funds = {}
        self.fold_table = {}
        self.pattern_memo = {}
        self.gcounter = 0
        self.tmp = 0
        self.spent = {}
        self._osz = {}
        self._attr = []
        self.hist = []
        self.stats = {"unfolded": 0, "folded": 0, "generalized": 0,
                      "bailed": 0, "nodes": 0}

    # ---------------- naming / accounting

    def fresh(self, base="r"):
        self.tmp += 1
        return "%s%d" % (base, self.tmp)

    def account(self, node):
        self.stats["nodes"] += 1
        if self._attr:
            fid = self._attr[-1]
            self.spent[fid] = self.spent.get(fid, 0) + _rt_size(node)

    # ---------------- entry

    def run(self):
        kind, pay = self._dt(self.anf["main"], {})
        if kind == "V":
            term = self.finalize(pay)
        elif kind == "R":
            term = pay
        elif kind == "X":
            term = ("rraise", ("rconst", pay))
        else:
            term = pay
        return {"funds": dict(self.res_funds), "main": term}

    def finalize(self, v):
        """Turn a final static value into residual code."""
        if is_case(v):
            rn = self.fresh()
            mat = self.materialize_case(v, rn)
            return seq_term(mat, ("rid", ("rvar", rn)))
        if isinstance(v, tuple) and v and v[0] == "scons":
            hd_a, hd_pre = self.finalize_atom(v[1])
            rn2 = self.fresh()
            rn = self.fresh()
            core = ("rlet", rn2, ("rsub", self.finalize(v[2])),
                    ("rlet", rn, ("rprim", "cons", [hd_a, ("rvar", rn2)]),
                     ("rid", ("rvar", rn))))
            return core if hd_pre is None else seq_term(hd_pre, core)
        if isinstance(v, tuple) and v and v[0] == "sclo":
            ras, pre = self.materialize_args(list(v[2]))
            rn = self.fresh()
            node = ("rlet", rn, ("rmkclo", v[1], ras), ("rid", ("rvar", rn)))
            return node if pre is None else seq_term(pre, node)
        if is_dyn(v):
            return ("rid", ("rvar", v[1]))
        return ("rid", ("rconst", v))

    def finalize_atom(self, v):
        if is_scalar(v):
            return (("rconst", v), None)
        if is_dyn(v):
            return (("rvar", v[1]), None)
        rn = self.fresh()
        t = self.finalize_to_term(v, rn)
        return (("rvar", rn), t)

    def finalize_to_term(self, v, rn):
        """Residual term that binds rn to the value of v."""
        if isinstance(v, tuple) and v and v[0] == "scons":
            hd_a, hd_pre = self.finalize_atom(v[1])
            rn2 = self.fresh()
            body = ("rlet", rn2, ("rsub", self.finalize(v[2])),
                    ("rlet", rn, ("rprim", "cons", [hd_a, ("rvar", rn2)]),
                     ("rid", ("rvar", rn))))
            return body if hd_pre is None else seq_term(hd_pre, body)
        if isinstance(v, tuple) and v and v[0] == "sclo":
            ras, pre = self.materialize_args(list(v[2]))
            body = ("rlet", rn, ("rmkclo", v[1], ras), ("rid", ("rvar", rn)))
            return body if pre is None else seq_term(pre, body)
        if is_case(v):
            raise AssertionError("case inside structure finalize")
        a, pre = self.finalize_atom(v)
        body = ("rlet", rn, ("rcopy", a), ("rid", ("rvar", rn)))
        return body if pre is None else seq_term(pre, body)

    # ---------------- configuration building

    def build_cfg(self, fid, body, env):
        slots = []
        names = []
        canon = {}

        def slot_of(name):
            s = canon.get(name)
            if s is None:
                s = len(slots)
                canon[name] = s
                slots.append(env.get(name))
                names.append(name)
            return s

        def vt(v, d=0):
            if d > 40:
                return ("#deep",)
            if is_scalar(v):
                return valtree(v)
            k = v[0]
            if k == "dyn":
                return ("D",)
            if k == "sclo":
                return ("#clo", v[1], tuple(vt(x, d + 1) for x in v[2]))
            if k == "scons":
                return ("#cons", vt(v[1], d + 1), vt(v[2], d + 1))
            return ("#CASE",)

        def atomt(a):
            if a[0] == "acon":
                return vt(a[1])
            return ("V", slot_of(a[1]))

        counter = [0]

        def tt(t, d=0):
            counter[0] += 1
            if counter[0] > self.opts.max_cfg_depth:
                return ("#deep",)
            tag = t[0]
            if tag == "ahalt":
                return ("#halt", atomt(t[1]))
            if tag == "araise":
                return ("#raise", atomt(t[1]))
            if tag == "alet":
                _, name, rhs, bod = t
                slot_of(name)  # register slot position (deterministic)
                return ("#let", rt(rhs), tt(bod))
            if tag == "aif":
                return ("#if", atomt(t[1]), tt(t[2]), tt(t[3]))
            if tag == "atry":
                _, name, b, h, cont = t
                slot_of(name)
                return ("#try", tt(b), atomt(h), tt(cont))
            raise AssertionError("cfg %r" % (tag,))

        def rt(rhs, d=0):
            tag = rhs[0]
            if tag == "aprim":
                return ("#p", rhs[1], tuple(atomt(a) for a in rhs[2]))
            if tag == "aapp":
                return ("#call", atomt(rhs[1]), tuple(atomt(a) for a in rhs[2]))
            if tag == "adirect":
                return ("#dcall", rhs[1], tuple(atomt(a) for a in rhs[2]))
            if tag == "amkclo":
                return ("#mk", rhs[1], tuple(atomt(a) for a in rhs[2]))
            if tag == "abox":
                return ("#box", atomt(rhs[1]))
            if tag == "aunbox":
                return ("#unbox", atomt(rhs[1]))
            if tag == "asetbox":
                return ("#setbox", atomt(rhs[1]), atomt(rhs[2]))
            if tag == "acopy":
                return ("#copy", atomt(rhs[1]))
            if tag == "rsub":
                return ("#sub", tt(rhs[1], d + 1))
            raise AssertionError("rt %r" % (tag,))

        tree = tt(body)
        return Cfg(fid, tree, slots, names)

    # ---------------- driving

    def _dt(self, t, env):
        tag = t[0]

        if tag == "ahalt":
            return self.value_result(self.resolve(t[1], env))

        if tag == "araise":
            v = self.resolve(t[1], env)
            if is_dyn(v):
                return ("RX", ("rraise", ("rvar", v[1])))
            if is_case(v):
                rn = self.fresh()
                mat = self.materialize_case(v, rn)
                return ("RX", seq_term(mat, ("rraise", ("rvar", rn))))
            return ("X", v)

        if tag == "alet":
            _, name, rhs, body = t
            out = self.rhs_result(name, rhs, env)

            if out[0] == "static":
                kb, pb = self._dt(body, out[2])
                return (kb, pb)

            if out[0] == "term":
                rr, env2 = out[1], out[2]
                if rr[0] not in _RRHS:
                    if rr[0] in ("rconst", "rvar"):
                        rr = ("rcopy", rr)
                    else:
                        rr = ("rsub", rr)
                kb, pb = self._dt(body, env2)
                inner = self.finish_body(kb, pb)
                node = ("rlet", name, rr, inner)
                self.account(node)
                if kb == "V":
                    return ("R", seq_term(node, self.value_tail(pb)))
                if kb == "X":
                    return ("RX", node)
                return (kb, node)

            if out[0] == "cstat":
                rr, v = out[1], out[2]
                kb, pb = self._dt(body, out[3])
                rn = self.fresh()
                inner = self.finish_body(kb, pb)
                node = ("rlet", rn, rr, inner)
                self.account(node)
                if kb == "V":
                    return ("R", seq_term(node, self.value_tail(pb)))
                if kb == "X":
                    return ("RX", node)
                return (kb, node)

            if out[0] == "split":
                cond_ra, vt_, ve_, envb = out[1], out[2], out[3], out[4]
                e1 = dict(envb); e1[name] = vt_
                e2 = dict(envb); e2[name] = ve_
                kt, pt = self._dt(body, e1)
                ke, pe = self._dt(body, e2)
                return self.merge(kt, pt, ke, pe, cond_ra)

            if out[0] == "xraise":
                return ("X", out[1])

            raise AssertionError("rhs out %r" % (out[0],))

        if tag == "aif":
            return self._aif(t, env)

        if tag == "atry":
            return self._atry(t, env)

        raise AssertionError("_dt %r" % (tag,))

    def value_tail(self, v):
        """Terminal term producing runtime value of v."""
        if is_scalar(v):
            return ("rid", ("rconst", v))
        if is_dyn(v):
            return ("rid", ("rvar", v[1]))
        rn = self.fresh()
        return self.finalize_to_term(v, rn)

    def finish_body(self, kb, pb):
        """Term for a continuation whose value is DISCARDED (effects kept).
        For R/RX the term itself already yields a value; wrapping sites that
        need the value must NOT route it through here."""
        if kb == "V":
            return ("rid", ("rconst", None))
        if kb == "R":
            return pb
        if kb == "X":
            return ("rraise", ("rconst", pb))
        return pb

    def value_result(self, v):
        if is_dyn(v):
            return ("R", ("rid", ("rvar", v[1])))
        if is_case(v):
            rn = self.fresh()
            mat = self.materialize_case(v, rn)
            return ("R", seq_term(mat, ("rid", ("rvar", rn))))
        return ("V", v)

    # ---- if

    def _aif(self, t, env):
        _, c, th, el = t
        cv = self.resolve(c, env)

        if is_scalar(cv):
            if isinstance(cv, bool):
                return self._dt(th if cv else el, env)
            return ("X", ("err", "err:if-condition-not-bool"))

        if is_case(cv):
            kt, pt = self._dt(th, env)
            ke, pe = self._dt(el, env)
            if _is_bool(cv[2]) and _is_bool(cv[3]):
                return self.merge(kt, pt, ke, pe, cv[1])
            rn = self.fresh()
            mat = self.materialize_case(cv, rn)
            merged = self.merge(kt, pt, ke, pe, ("rvar", rn))
            return self.after_mat(mat, merged)

        if is_dyn(cv):
            kt, pt = self._dt(th, env)
            ke, pe = self._dt(el, env)
            return self.merge(kt, pt, ke, pe, ("rvar", cv[1]))

        return ("X", ("err", "err:if-condition-not-bool"))

    def after_mat(self, mat, merged):
        k, p = merged
        if k == "V":
            return ("R", seq_term(mat, ("rid", ("rconst", p))))
        if k == "R":
            return ("R", seq_term(mat, p))
        if k == "X":
            return ("RX", seq_term(mat, ("rraise", ("rconst", p))))
        return ("RX", seq_term(mat, p))

    # ---- try

    def _atry(self, t, env):
        _, name, bterm, hatom, cont = t
        hv = self.resolve(hatom, env)
        kb, pb = self._dt(bterm, env)

        if kb == "X":
            return self.apply_handler(hv, pb, name, env, cont)

        if kb == "V":
            env2 = dict(env)
            env2[name] = pb
            return self._dt(cont, env2)

        hn = self.fresh("h")
        hterm = self.value_to_rhs(hv)
        env2 = dict(env)
        env2[name] = ("dyn", name)
        kc, pc = self._dt(cont, env2)
        inner = self.finish_body(kc, pc)
        node = ("rlet", hn, hterm,
                ("rlet", name, ("rtry", pb, ("rvar", hn)), inner))
        self.account(node)
        if kc == "V":
            return ("R", seq_term(node, self.value_tail(pc)))
        if kc == "X":
            return ("RX", node)
        return (kc, node)

    def apply_handler(self, hv, payload, binder, env, cont):
        if hv[0] == "sclo":
            res = self.unfold_sclo(hv, [payload])
            if res[0] == "sx":
                return ("X", res[1])
            if res[0] == "sv":
                v = res[1]
                if is_case(v):
                    rn = self.fresh()
                    mat = self.materialize_case(v, rn)
                    env2 = dict(env); env2[binder] = ("dyn", rn)
                    kc, pc = self._dt(cont, env2)
                    node = seq_term(mat, self.finish_body(kc, pc))
                    if kc == "V":
                        return ("R", seq_term(node, self.value_tail(pc)))
                    if kc == "X":
                        return ("RX", node)
                    return (kc, node)
                env2 = dict(env); env2[binder] = v
                return self._dt(cont, env2)
            rn = self.fresh()
            env2 = dict(env); env2[binder] = ("dyn", rn)
            kc, pc = self._dt(cont, env2)
            node = ("rlet", rn, ("rsub", res[1]), self.finish_body(kc, pc))
            self.account(node)
            if kc == "V":
                return ("R", seq_term(node, self.value_tail(pc)))
            if kc == "X":
                return ("RX", node)
            return (kc, node)

        if is_dyn(hv):
            hn = self.fresh("h")
            pa = ("rconst", payload) if is_scalar(payload) else None
            pre = None
            if pa is None:
                pm = self.fresh()
                pre = ("rlet", pm, self.value_to_rhs(payload),
                       ("rid", ("rvar", pm)))
                pa = ("rvar", pm)
            env2 = dict(env); env2[binder] = ("dyn", binder)
            kc, pc = self._dt(cont, env2)
            inner = ("rlet", binder,
                     ("rexp", ("rcall", ("rvar", hn), [pa])),
                     self.finish_body(kc, pc))
            node = ("rlet", hn, ("rcopy", ("rvar", hv[1])), inner)
            if pre is not None:
                node = seq_term(pre, node)
            self.account(node)
            if kc == "V":
                return ("R", seq_term(node, self.value_tail(pc)))
            if kc == "X":
                return ("RX", node)
            return (kc, node)

        return ("X", ("err", "err:call-of-non-closure"))

    # ---- rhs evaluation

    def rhs_result(self, name, rhs, env):
        tag = rhs[0]

        if tag == "acopy":
            v = self.resolve(rhs[1], env)
            if is_case(v):
                return ("split", v[1], v[2], v[3], env)
            env2 = dict(env); env2[name] = v
            return ("static", v, env2)

        if tag == "aprim":
            return self.prim_rhs(name, rhs[1], rhs[2], env)

        if tag == "aapp":
            fv = self.resolve(rhs[1], env)
            argvs = [self.resolve(a, env) for a in rhs[2]]

            if is_case(fv):
                rn_c = self.fresh()
                mat = self.materialize_case(fv, rn_c)
                ras = [self.arg_atom(v) for v in argvs]
                rn = self.fresh()
                term = ("rexp", ("rcall", ("rvar", rn_c), ras))
                return ("term", seq_term(mat, term),
                        dict(env, **{name: ("dyn", name)}))

            if is_dyn(fv):
                ras = [self.arg_atom(v) for v in argvs]
                rn = self.fresh()
                return ("term", ("rcall", ("rvar", fv[1]), ras),
                        dict(env, **{name: ("dyn", name)}))

            if fv[0] == "sclo":
                res = self.unfold_sclo(fv, argvs)
                return self.unfold_out(res, name, env)

            return ("xraise", ("err", "err:call-of-non-closure"))

        if tag == "adirect":
            argvs = [self.resolve(a, env) for a in rhs[2]]
            ras, pre = self.materialize_args(argvs)
            rn = self.fresh()
            term = ("rexp", ("rdirect", rhs[1], ras))
            if pre is not None:
                term = seq_term(pre, term)
            return ("term", term, dict(env, **{name: ("dyn", name)}))

        if tag == "amkclo":
            fvs = [self.resolve(a, env) for a in rhs[2]]
            if all(context_free(v) for v in fvs):
                v = ("sclo", rhs[1], tuple(fvs))
                env2 = dict(env); env2[name] = v
                return ("static", v, env2)
            ras, pre = self.materialize_args(fvs)
            rn = self.fresh()
            term = ("rexp", ("rmkclo", rhs[1], ras))
            if pre is not None:
                term = seq_term(pre, term)
            return ("term", term, dict(env, **{name: ("dyn", name)}))

        if tag == "abox":
            ra, pre = self.mat_arg(self.resolve(rhs[1], env))
            rn = self.fresh()
            term = ("rexp", ("rbox", ra))
            if pre is not None:
                term = seq_term(pre, term)
            return ("term", term, dict(env, **{name: ("dyn", name)}))

        if tag == "aunbox":
            ra, pre = self.mat_arg(self.resolve(rhs[1], env))
            rn = self.fresh()
            term = ("rexp", ("runbox", ra))
            if pre is not None:
                term = seq_term(pre, term)
            return ("term", term, dict(env, **{name: ("dyn", name)}))

        if tag == "asetbox":
            r1, p1 = self.mat_arg(self.resolve(rhs[1], env))
            r2, p2 = self.mat_arg(self.resolve(rhs[2], env))
            rr = ("rprim", "set-box!", [r1, r2])
            if p1 is not None or p2 is not None:
                pre = combine_pre(p1, p2)
                return ("cstat", seq_term(pre, rr) if pre else rr, None, env)
            return ("cstat", rr, None, env)

        if tag == "rsub":
            rn = self.fresh()
            return ("term", ("rsub", rhs[1]), dict(env, **{name: ("dyn", name)}))

        raise AssertionError("rhs %r" % (tag,))

    def prim_rhs(self, name, p, args, env):
        vs = [self.resolve(a, env) for a in args]

        ci = next((i for i, v in enumerate(vs) if is_case(v)), None)
        if ci is not None and p in PURE_PRIMS:
            st = self.try_static(p, vs)
            if st is not None:
                kind, v = st
                if kind == "raise":
                    return ("xraise", v)
                if is_case(v):
                    return ("split", v[1], v[2], v[3], env)
                env2 = dict(env); env2[name] = v
                return ("static", v, env2)
            # distribute failed -> materialize case arg, op dynamically
            rn_m = self.fresh()
            mat = self.materialize_case(vs[ci], rn_m)
            vs2 = list(vs)
            vs2[ci] = ("dyn", rn_m)
            ras = [self.arg_atom(v) for v in vs2]
            rn = self.fresh()
            term = seq_term(mat, ("rexp", ("rprim", p, ras)))
            return ("term", term, dict(env, **{name: ("dyn", name)}))

        if p in ("print", "set-box!"):
            ras, pre = self.materialize_args(vs)
            rr = ("rprim", p, ras)
            if pre is not None:
                rr = seq_term(pre, rr)
            return ("cstat", rr, None, env)

        if p in ("unbox", "box"):
            ra, pre = self.mat_arg(vs[0])
            rn = self.fresh()
            term = ("rexp", ("rprim", p, [ra]))
            if pre is not None:
                term = seq_term(pre, term)
            return ("term", term, dict(env, **{name: ("dyn", name)}))

        st = self.try_static(p, vs)
        if st is not None:
            kind, v = st
            if kind == "raise":
                return ("xraise", v)
            if is_case(v):
                return ("split", v[1], v[2], v[3], env)
            env2 = dict(env); env2[name] = v
            return ("static", v, env2)

        ras, pre = self.materialize_args(vs)
        rn = self.fresh()
        term = ("rexp", ("rprim", p, ras))
        if pre is not None:
            term = seq_term(pre, term)
        return ("term", term, dict(env, **{name: ("dyn", name)}))

    def try_static(self, p, vs):
        """Symbolic static evaluation of a PURE primitive.
        Returns ('val', v) | ('raise', payload) | None (cannot decide)."""
        if any(is_dyn(v) or is_case(v) for v in vs):
            return None
        try:
            return ("val", eval_sym_prim(p, list(vs)))
        except ScmError as e:
            return ("raise", ("err", e.msg))
        except Exception:
            return ("raise", ("err", "err:prim-failed"))

    # ---- unfold / fold / generalize

    def unfold_sclo(self, sclo, args):
        fid = sclo[1]
        frees = list(sclo[2])
        params, body = self.funds[fid]
        nf = len(frees)

        if not self.may_specialize(fid):
            return self.bail_direct(sclo, args)

        env2 = {}
        for i, p in enumerate(params[:nf]):
            env2[p] = frees[i]
        for i, p in enumerate(params[nf:]):
            env2[p] = args[i]

        cfg = self.build_cfg(fid, body, env2)

        fe = self.find_fold(cfg)
        if fe is not None:
            self.stats["folded"] += 1
            return self.emit_fold_call(fe, cfg)

        if self.whistle_ancestor(cfg) is not None:
            if self.generalize(cfg):
                fe = self.find_fold(cfg)
                if fe is not None:
                    self.stats["folded"] += 1
                    return self.emit_fold_call(fe, cfg)

        if len(self.hist) >= self.opts.max_history:
            return self.bail_direct(sclo, args)

        self.stats["unfolded"] += 1
        self.hist.append(cfg)
        self._attr.append(fid)
        try:
            kb, pb = self._dt(body, env2)
        finally:
            self.hist.pop()
            self._attr.pop()
        if kb == "V":
            return ("sv", pb)
        if kb == "R":
            self.account(pb)
            return ("term", pb)
        if kb == "X":
            return ("sx", pb)
        self.account(pb)
        return ("term", pb)

    def unfold_out(self, res, name, env):
        if res[0] == "sv":
            v = res[1]
            if is_case(v):
                return ("split", v[1], v[2], v[3], env)
            env2 = dict(env); env2[name] = v
            return ("static", v, env2)
        if res[0] == "sx":
            return ("xraise", res[1])
        rn = self.fresh()
        return ("term", ("rsub", res[1]), dict(env, **{name: ("dyn", name)}))

    def may_specialize(self, fid):
        o = self.opts
        if not o.specialize or fid in o.no_specialize:
            return False
        budget = o.per_func_budget.get(fid, o.expand_factor)
        return self.spent.get(fid, 0) <= budget * self.orig_size(fid)

    def orig_size(self, fid):
        if fid not in self._osz:
            self._osz[fid] = float(max(1, _anf_size(self.funds[fid][1])))
        return self._osz[fid]

    def bail_direct(self, sclo, args):
        """Residual direct call to the ORIGINAL fund."""
        self.stats["bailed"] += 1
        ras, pre = self.materialize_args(list(sclo[2]) + list(args))
        term = ("rexp", ("rdirect", sclo[1], ras))
        if pre is not None:
            term = seq_term(pre, term)
        return ("term", term)

    def emit_fold_call(self, fe, cfg):
        ras = []
        for slot in fe.params:
            a = self.extract_atom(cfg.slots[slot])
            ras.append(a)
        return ("term", ("rexp", ("rdirect", fe.gname, ras)))

    # ---- whistle & generalization

    def whistle_ancestor(self, cfg):
        run = 0
        for i in range(len(self.hist) - 1, -1, -1):
            anc = self.hist[i]
            if anc.fid != cfg.fid:
                if run:
                    break
                continue
            run += 1
            if len(anc.slots) != len(cfg.slots):
                continue
            try:
                hit = HE.embed(anc.as_tree(), cfg.as_tree())
            except RecursionError:
                hit = True
            if hit:
                if run >= self.opts.min_repeat:
                    return anc
        return None

    def generalize(self, cur):
        anc = self.whistle_ancestor(cur)
        if anc is None:
            return False

        nslots = min(len(anc.slots), len(cur.slots))
        fixed = {}
        params = []

        for k in range(nslots):
            va = anc.slots[k]
            vc = cur.slots[k]
            if va is None and vc is None:
                continue
            if vc is None:
                if va is not None and context_free(va):
                    fixed[k] = va
                    continue
                return False
            if va is None:
                if self.extractable(vc):
                    params.append(k)
                    continue
                return False
            if val_eq(va, vc) and context_free(va):
                fixed[k] = va
                continue
            if self.extractable(vc):
                params.append(k)
                continue
            if context_free(va):
                fixed[k] = va
                continue
            return False

        if not params:
            return False

        key_fixed = tuple(sorted((k, freeze_val(v)) for k, v in fixed.items()))
        pkey = (cur.fid, key_fixed, tuple(params), nslots)
        gname = self.pattern_memo.get(pkey)
        if gname is None:
            gname = self.gen_gname(cur.fid)
            gparams = ["q%d" % i for i in range(len(params))]
            pat_env = {}
            for k, v in fixed.items():
                pat_env[cur.names[k]] = v
            for k, qn in zip(params, gparams):
                pat_env[cur.names[k]] = ("dyn", qn)
            self.pattern_memo[pkey] = gname
            self._attr.append(cur.fid)
            try:
                kb, pb = self._dt(self.funds[cur.fid][1], pat_env)
            finally:
                self._attr.pop()
            if kb == "V":
                gbody = ("rid", ("rconst", pb))
            elif kb == "R":
                gbody = pb
            elif kb == "X":
                gbody = ("rraise", ("rconst", pb))
            else:
                gbody = pb
            self.res_funds[gname] = (list(gparams), gbody)
            if len(self.res_funds) > self.opts.max_funcs:
                raise Bail()
        self.register_fold(gname, cur.fid, fixed, params, nslots)
        self.stats["generalized"] += 1
        return True

    def register_fold(self, gname, fid, fixed, params, nslots):
        key = (fid, tuple(sorted((k, freeze_val(v))
                                 for k, v in fixed.items())))
        self.fold_table.setdefault(key, []).append(
            FoldEntry(gname, fid, dict(fixed), list(params), nslots))

    def find_fold(self, cfg):
        for (fid, _fk), entries in self.fold_table.items():
            if fid != cfg.fid:
                continue
            for fe in entries:
                if fe.nslots != len(cfg.slots):
                    continue
                ok = True
                for k, v in fe.fixed.items():
                    if not val_eq(v, cfg.slots[k]):
                        ok = False
                        break
                if not ok:
                    continue
                for k in fe.params:
                    if not self.extractable(cfg.slots[k]):
                        ok = False
                        break
                if ok:
                    return fe
        return None

    def gen_gname(self, fid):
        self.gcounter += 1
        return "%s$g%d" % (fid.replace(".", "_").replace("$", "_"),
                           self.gcounter)

    # ---- small helpers

    def resolve(self, a, env):
        if a[0] == "acon":
            return a[1]
        return env[a[1]]

    def extractable(self, v):
        if v is None:
            return False
        return is_scalar(v) or is_dyn(v)

    def extract_atom(self, v):
        if is_dyn(v):
            return ("rvar", v[1])
        return ("rconst", v)

    def arg_atom(self, v):
        if is_dyn(v):
            return ("rvar", v[1])
        if is_scalar(v):
            return ("rconst", v)
        raise AssertionError("complex value in strict arg position: %r" % (v,))

    def mat_arg(self, v):
        """atom plus optional pre-statement materializing complex values."""
        if is_scalar(v) or is_dyn(v):
            return self.arg_atom(v), None
        rn = self.fresh()
        return ("rvar", rn), ("rlet", rn, self.value_to_rhs(v),
                              ("rid", ("rvar", rn)))

    def materialize_args(self, vs):
        ras = []
        pres = []
        for v in vs:
            a, pre = self.mat_arg(v)
            ras.append(a)
            if pre is not None:
                pres.append(pre)
        return ras, combine_pre(*pres)

    def value_to_rhs(self, v):
        """RRhs producing the runtime value of v."""
        if is_dyn(v):
            return ("rcopy", ("rvar", v[1]))
        if is_case(v):
            rn = self.fresh()
            mat = self.materialize_case(v, rn)
            return ("rsub", seq_term(mat, ("rid", ("rvar", rn))))
        if isinstance(v, tuple) and v and v[0] in ("scons", "sclo"):
            rn = self.fresh()
            return ("rsub", self.finalize_to_term(v, rn))
        return ("rconst", v)

    def materialize_case(self, cas, rn):
        _, cond_ra, vt_, ve_ = cas
        return ("rlet", rn,
                ("rifv", cond_ra, self.branch_atom(vt_), self.branch_atom(ve_)),
                ("rid", ("rvar", rn)))

    def branch_atom(self, v):
        if is_dyn(v):
            return ("rvar", v[1])
        return ("rconst", v)

    def branch_value(self, v):
        """Runtime-representable atom for a branch arm; materializes
        symbolic structures into fresh temps when necessary."""
        if is_scalar(v):
            return ("rconst", v)
        if is_dyn(v):
            return ("rvar", v[1])
        # complex static value: cannot appear inline; caller context makes
        # this impossible in practice, but stay sound by failing loudly.
        raise AssertionError("complex branch value %r" % (v,))

    def merge(self, kt, pt, ke, pe, cond_ra):
        if kt == "V" and ke == "V":
            if val_eq(pt, pe):
                return ("V", pt)
            ta, prea = self.mat_arg(pt)
            tb, preb = self.mat_arg(pe)
            rn = self.fresh()
            sel = ("rlet", rn,
                   ("rifv", cond_ra, ta, tb),
                   ("rid", ("rvar", rn)))
            node = sel
            if prea is not None or preb is not None:
                pre = combine_pre(prea, preb)
                node = seq_term(pre, sel) if pre else sel
            self.account(node)
            return ("R", node)
        t1 = self.side_to_term(kt, pt)
        t2 = self.side_to_term(ke, pe)
        node = ("rif", cond_ra, t1, t2)
        self.account(node)
        return ("R", node)

    def side_to_term(self, k, p):
        if k in ("R", "RX"):
            return p
        if k == "V":
            if is_scalar(p) or is_dyn(p):
                a = self.extract_atom(p)
                return ("rid", a)
            rn = self.fresh()
            return self.finalize_to_term(p, rn)
        if k == "X":
            return ("rraise", ("rconst", p))
        raise AssertionError(k)


# ------------------------------------------------------------- utilities

_INT_OPS = {"+", "-", "*", "quot", "rem", "<", ">", "<=", ">=", "=",
            "abs", "min", "max"}


def eval_sym_prim(p, vs):
    """Static evaluation over the symbolic value domain.
    Mirrors sc.semantics.prim exactly, extended to symbolic pairs."""
    from .semantics import Pair

    def need_int(v):
        if isinstance(v, bool) or not isinstance(v, int):
            raise ScmError("err:non-int-operand")
        return v

    if p == "cons":
        return ("scons", vs[0], vs[1])
    if p == "car":
        v = vs[0]
        if v is None:
            raise ScmError("err:car-of-non-pair")
        if isinstance(v, tuple) and v and v[0] == "scons":
            return v[1]
        if is_scalar(v):
            raise ScmError("err:car-of-non-pair")
        raise AssertionError("car of %r" % (v,))
    if p == "cdr":
        v = vs[0]
        if v is None:
            raise ScmError("err:cdr-of-non-pair")
        if isinstance(v, tuple) and v and v[0] == "scons":
            return v[2]
        if is_scalar(v):
            raise ScmError("err:cdr-of-non-pair")
        raise AssertionError
    if p == "pair?":
        v = vs[0]
        if isinstance(v, tuple) and v and v[0] == "scons":
            return True
        if is_dyn(v) or is_case(v):
            raise AssertionError("unreduced case/dyn in pair?")
        return False
    if p == "null?":
        v = vs[0]
        if v is None:
            return True
        if isinstance(v, tuple) and v and v[0] == "scons":
            return False
        if is_scalar(v):
            return False
        raise AssertionError
    if p == "procedure?":
        v = vs[0]
        return isinstance(v, tuple) and v and v[0] == "sclo"
    if p == "box?":
        return False  # boxes are never static values
    if p == "not":
        v = vs[0]
        if not isinstance(v, bool):
            raise ScmError("err:not-of-non-bool")
        return not v
    if p == "eq?" or p == "equal?":
        a, b = vs
        if is_case(a) or is_case(b) or is_dyn(a) or is_dyn(b):
            raise AssertionError
        if a is None or b is None:
            return a is b
        if isinstance(a, bool) or isinstance(b, bool):
            return a is b
        if isinstance(a, int) and isinstance(b, int):
            return a == b
        if hasattr(a, "name") and hasattr(b, "name"):
            return a.name == b.name
        if isinstance(a, tuple) and a and a[0] == "err":
            return isinstance(b, tuple) and b and b[0] == "err" \
                and a[1] == b[1]
        if isinstance(a, tuple) and a and a[0] == "scons" and \
                isinstance(b, tuple) and b and b[0] == "scons":
            return val_eq(a, b)
        # closures / mixed types: identity (structural for sclo is safe:
        # same fid+frees behave identically)
        if isinstance(a, tuple) and a and a[0] == "sclo" and \
                isinstance(b, tuple) and b and b[0] == "sclo":
            return val_eq(a, b)
        return False
    if p in _INT_OPS:
        vs = [need_int(v) for v in vs]
        return apply_prim(p, vs)
    raise AssertionError("eval_sym_prim %s" % p)


def _is_bool(v):
    return isinstance(v, bool)


def combine_pre(*pres):
    ps = [p for p in pres if p is not None]
    if not ps:
        return None
    t = ps[0]
    for p in ps[1:]:
        t = seq_term(t, p)
    return t


def _rt_size(t, cap=20000):
    n = 0
    stack = [t]
    while stack:
        x = stack.pop()
        if isinstance(x, tuple):
            n += 1
            if n > cap:
                break
            stack.extend(x[1:])
    return n


def _anf_size(t, cap=100000):
    n = 0
    stack = [t]
    while stack:
        x = stack.pop()
        if isinstance(x, tuple) and x and isinstance(x[0], str):
            n += 1
            if n > cap:
                break
            stack.extend(x[1:])
    return max(1, n)


def seq_term(prefix, suffix):
    """Append suffix after value-producing prefix term."""
    tag = prefix[0]
    if tag == "rlet":
        return ("rlet", prefix[1], prefix[2], seq_term(prefix[3], suffix))
    if tag == "rif":
        return ("rif", prefix[1],
                seq_term(prefix[2], suffix), seq_term(prefix[3], suffix))
    return suffix
