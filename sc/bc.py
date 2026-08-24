"""Bytecode compiler: unified IR -> linear code for the VM.

IR terms (driver residual terms are a subset of these):
  ('ahalt', atom) | ('araise', atom)
  ('alet', name, rhs, body)
  ('aif', cond_atom, then_term, else_term)
  ('atry', name, body_term, handler_atom, cont_term)      [front-end form]
  ('rid', atom) | ('rraise', atom)                        [value terminals]
  ('rlet', name, rhs, body) | ('rif', c, t, e) | ('rexp', rhs)

rhs kinds:
  ('aprim'|'rprim', p, [a])   ('aapp', f, [a])    ('rcall', f, [a])
  ('adirect', fid, [a])       ('amkclo', fid, [a])
  ('abox', a) ('aunbox', a) ('asetbox', a1, a2)
  ('acopy', a) | ('rcopy', a)
  ('rsub', term)              -- nested term produces the value
  ('rifv', c, a_then, a_else) -- value-producing if over atoms
  ('rtry', term, handler_atom)-- runtime try; exceptions call handler(exc)
"""
from __future__ import annotations


class FundCode:
    __slots__ = ("name", "nparams", "nlocals", "code")

    def __init__(self, name, nparams, code):
        self.name = name
        self.nparams = nparams
        self.code = code
        self.nlocals = nparams


class BytecodeProgram:
    def __init__(self, funds, main, meta=None):
        self.funds = funds
        self.main = main
        self.meta = meta or {}

    def total_instructions(self):
        n = len(self.main.code)
        for f in self.funds.values():
            n += len(f.code)
        return n


def compile_ir(irprog: dict) -> BytecodeProgram:
    funds = {}
    for fid, (params, term) in irprog["funds"].items():
        g = _Gen(params, ("ret",))
        g.term(term)
        f = FundCode(fid, len(params), g.code)
        f.nlocals = g.next_local
        funds[fid] = f
    g = _Gen([], ("halt",))
    g.term(irprog["main"])
    main = FundCode("main", 0, g.code)
    main.nlocals = g.next_local
    return BytecodeProgram(funds, main)


class _Gen:
    def __init__(self, params, terminal):
        self.locs = {p: i for i, p in enumerate(params)}
        self.next_local = len(params)
        self.code = []
        self.terminal = terminal

    def newlocal(self):
        i = self.next_local
        self.next_local += 1
        return i

    def emit(self, *ins):
        self.code.append(ins)

    def load_atom(self, a):
        if a[0] in ("acon", "rconst"):
            self.emit("const", a[1])
        elif a[0] in ("avar", "rvar"):
            self.emit("load", self.locs[a[1]])
        else:
            raise AssertionError("bad atom %r" % (a,))

    # ---------------- terms

    def term(self, t):
        tag = t[0]
        if tag == "ahalt" or tag == "rid":
            self.load_atom(t[1])
            m = self.terminal
            if m[0] == "store":
                self.emit("store", m[1])
            else:
                self.emit(m[0])
        elif tag == "araise" or tag == "rraise":
            self.load_atom(t[1])
            self.emit("raise")
        elif tag in ("alet", "rlet"):
            _, name, rhs, body = t
            idx = self.newlocal()
            self.gen_rhs(idx, rhs)
            self.bind(name, idx, body)
        elif tag == "aif" or tag == "rif":
            _, c, th, el = t
            self.load_atom(c)
            j_else = len(self.code)
            self.emit("jiff", None)
            self.term(th)
            j_end = len(self.code)
            self.emit("jmp", None)
            self.code[j_else] = ("jiff", len(self.code))
            self.term(el)
            self.code[j_end] = ("jmp", len(self.code))
        elif tag == "atry":
            _, name, bterm, hatom, cont = t
            val_i = self.newlocal()
            exc_i = self.newlocal()
            h_pos = len(self.code)
            self.emit("try", None)
            saved = self.terminal
            self.terminal = ("store", val_i)
            self.term(bterm)
            self.terminal = saved
            self.emit("endtry")
            j_end = len(self.code)
            self.emit("jmp", None)
            self.code[h_pos] = ("try", len(self.code))
            self.emit("store", exc_i)
            self.load_atom(hatom)
            self.emit("load", exc_i)
            self.emit("call", 1)
            self.emit("store", val_i)
            self.code[j_end] = ("jmp", len(self.code))
            self.bind(name, val_i, cont)
        elif tag == "rexp":
            idx = self.newlocal()
            self.gen_rhs(idx, t[1])
            self.emit("load", idx)
            m = self.terminal
            if m[0] == "store":
                self.emit("store", m[1])
            else:
                self.emit(m[0])
        else:
            raise AssertionError("bad term %r" % (tag,))

    def bind(self, name, idx, body):
        prev = self.locs.get(name)
        self.locs[name] = idx
        try:
            self.term(body)
        finally:
            if prev is None:
                del self.locs[name]
            else:
                self.locs[name] = prev

    # ---------------- right-hand sides

    def gen_rhs(self, idx, rr):
        tag = rr[0]
        if tag in ("aprim", "rprim"):
            _, p, args = rr
            for a in args:
                self.load_atom(a)
            self.emit("prim", p, len(args))
            self.emit("store", idx)
        elif tag in ("aapp", "rcall"):
            _, fa, args = rr
            self.load_atom(fa)
            for a in args:
                self.load_atom(a)
            self.emit("call", len(args))
            self.emit("store", idx)
        elif tag == "adirect":
            _, fid, args = rr
            for a in args:
                self.load_atom(a)
            self.emit("calld", fid, len(args))
            self.emit("store", idx)
        elif tag == "rdirect":
            _, fid, args = rr
            for a in args:
                self.load_atom(a)
            self.emit("calld", fid, len(args))
            self.emit("store", idx)
        elif tag == "amkclo" or tag == "rmkclo":
            _, fid, frees = rr
            for a in frees:
                self.load_atom(a)
            self.emit("clo", fid, len(frees))
            self.emit("store", idx)
        elif tag in ("abox", "rbox"):
            self.load_atom(rr[1])
            self.emit("prim", "box", 1)
            self.emit("store", idx)
        elif tag in ("aunbox", "runbox"):
            self.load_atom(rr[1])
            self.emit("prim", "unbox", 1)
            self.emit("store", idx)
        elif tag in ("asetbox", "rsetbox"):
            self.load_atom(rr[1])
            self.load_atom(rr[2])
            self.emit("prim", "set-box!", 2)
            self.emit("store", idx)
        elif tag in ("acopy", "rcopy"):
            self.load_atom(rr[1])
            self.emit("store", idx)
        elif tag == "rsub":
            saved = self.terminal
            self.terminal = ("store", idx)
            self.term(rr[1])
            self.terminal = saved
        elif tag == "rexp":
            self.gen_rhs(idx, rr[1])
        elif tag == "rifv":
            _, c, at, ae = rr
            self.load_atom(c)
            j_else = len(self.code)
            self.emit("jiff", None)
            self.load_atom(at)
            j_end = len(self.code)
            self.emit("jmp", None)
            self.code[j_else] = ("jiff", len(self.code))
            self.load_atom(ae)
            self.code[j_end] = ("jmp", len(self.code))
            self.emit("store", idx)
        elif tag == "rtry":
            _, bterm, hra = rr
            exc_i = self.newlocal()
            h_pos = len(self.code)
            self.emit("try", None)
            saved = self.terminal
            self.terminal = ("store", idx)
            self.term(bterm)
            self.terminal = saved
            self.emit("endtry")
            j_end = len(self.code)
            self.emit("jmp", None)
            self.code[h_pos] = ("try", len(self.code))
            self.emit("store", exc_i)
            self.load_atom(hra)
            self.emit("load", exc_i)
            self.emit("call", 1)
            self.emit("store", idx)
            self.code[j_end] = ("jmp", len(self.code))
        else:
            # generic fallback: any TERM can act as a value producer
            saved = self.terminal
            self.terminal = ("store", idx)
            try:
                self.term(rr)
            finally:
                self.terminal = saved
