"""Decompile unified IR back to SC-Lang source (idempotence checking,
residual inspection)."""
from __future__ import annotations

from .sexp import pretty

FUNDS = {}


def _atom(a):
    k = a[0]
    if k in ("acon", "rconst"):
        v = a[1]
        if v is None:
            return "'()"
        if isinstance(v, bool):
            return "#t" if v else "#f"
        if hasattr(v, "name"):
            return "'" + v.name
        if isinstance(v, tuple) and v and v[0] == "err":
            raise ValueError("internal error payload cannot be decompiled")
        return str(v)
    if k in ("avar", "rvar"):
        return a[1]
    raise AssertionError("atom %r" % (a,))


def _mkclo(fid, free_atoms):
    params, body = FUNDS[fid]
    nf = len(free_atoms)
    inner = ["lambda", list(params[nf:]), _term(body)]
    if nf == 0:
        return inner
    outer = ["lambda", list(params[:nf]), inner]
    return [outer] + [_atom(a) for a in free_atoms]


def _rhs(rr):
    tag = rr[0]
    if tag in ("aprim", "rprim"):
        return [rr[1]] + [_atom(a) for a in rr[2]]
    if tag in ("aapp", "rcall"):
        return [_atom(rr[1])] + [_atom(a) for a in rr[2]]
    if tag == "adirect":
        return [rr[1]] + [_atom(a) for a in rr[2]]
    if tag in ("amkclo", "rmkclo"):
        return _mkclo(rr[1], rr[2])
    if tag in ("abox", "rbox"):
        return ["box", _atom(rr[1])]
    if tag in ("aunbox", "runbox"):
        return ["unbox", _atom(rr[1])]
    if tag in ("asetbox", "rsetbox"):
        return ["set-box!", _atom(rr[1]), _atom(rr[2])]
    if tag in ("acopy", "rcopy"):
        return _atom(rr[1])
    if tag == "rifv":
        return ["if", _atom(rr[1]), _atom(rr[2]), _atom(rr[3])]
    if tag == "rsub":
        return _term_expr(rr[1])
    if tag == "rtry":
        return ["try", _term_expr(rr[1]), _atom(rr[2])]
    if tag == "rexp":
        return _rhs(rr[1])
    raise AssertionError("rhs %r" % (tag,))


def _term(t):
    """Render term as statement-ish expression (value of last expr)."""
    tag = t[0]
    if tag in ("ahalt", "rid"):
        return _atom(t[1])
    if tag in ("araise", "rraise"):
        return ["raise", _atom(t[1])]
    if tag in ("alet", "rlet"):
        return ["let", [[t[1], _rhs(t[2])]], _term(t[3])]
    if tag in ("aif", "rif"):
        return ["if", _atom(t[1]), _term(t[2]), _term(t[3])]
    if tag == "atry":
        return ["let", [[t[1], ["try", _term_expr(t[2]), _atom(t[3])]]],
                _term(t[4])]
    if tag == "rexp":
        return _rhs(t[1])
    raise AssertionError("term %r" % (tag,))


def _term_expr(t):
    return _term(t)


def program_to_source(prog: dict) -> str:
    FUNDS.clear()
    FUNDS.update(prog["funds"])
    parts = []
    for fid, (params, term) in prog["funds"].items():
        parts.append(["define", [fid] + list(params), _term(term)])
    parts.append(_term(prog["main"]))
    return "\n".join(pretty(p) + "\n" for p in parts)
