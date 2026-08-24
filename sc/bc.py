"""Bytecode compiler: IR (ANF-shaped terms) -> linear code for the VM.

Terminal mode: every function body is generated with a "terminal mode"
telling `ahalt` what to do: emit `ret`, emit `halt` (main), or store the
value into a local (used when generating try-body blocks).
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
        funds[fid] = _gen_fund(fid, params, term, ("ret",))
    main = _gen_fund("main", [], irprog["main"], ("halt",))
    return BytecodeProgram(funds, main)


def _gen_fund(name, params, term, terminal):
    g = _Gen(params, terminal)
    g.term(term)
    f = FundCode(name, len(params), g.code)
    f.nlocals = g.next_local
    return f


class _Gen:
    def __init__(self, params, terminal):
        self.locs = {p: i for i, p in enumerate(params)}
        self.next_local = len(params)
        self.code = []
        self.terminal = terminal  # ("ret",) | ("halt",) | ("store", idx)

    def newlocal(self):
        i = self.next_local
        self.next_local += 1
        return i

    def emit(self, *ins):
        self.code.append(ins)

    def load_atom(self, a):
        if a[0] == "acon":
            self.emit("const", a[1])
        elif a[0] == "avar":
            self.emit("load", self.locs[a[1]])
        else:
            raise AssertionError("bad atom %r" % (a,))

    def term(self, t):
        tag = t[0]
        if tag == "ahalt":
            self.load_atom(t[1])
            m = self.terminal
            if m[0] == "store":
                self.emit("store", m[1])
            else:
                self.emit(m[0])
        elif tag == "araise":
            self.load_atom(t[1])
            self.emit("raise")
        elif tag == "alet":
            self.alet(t)
        elif tag == "aif":
            self.aif(t)
        elif tag == "atry":
            self.atry(t)
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

    def alet(self, t):
        _, name, rhs, body = t
        idx = self.newlocal()
        rtag = rhs[0]
        if rtag == "aprim":
            _, p, args = rhs
            for a in args:
                self.load_atom(a)
            self.emit("prim", p, len(args))
            self.emit("store", idx)
        elif rtag == "aapp":
            _, fa, args = rhs
            self.load_atom(fa)
            for a in args:
                self.load_atom(a)
            self.emit("call", len(args))
            self.emit("store", idx)
        elif rtag == "adirect":
            _, fid, args = rhs
            for a in args:
                self.load_atom(a)
            self.emit("calld", fid, len(args))
            self.emit("store", idx)
        elif rtag == "amkclo":
            _, fid, frees = rhs
            for a in frees:
                self.load_atom(a)
            self.emit("clo", fid, len(frees))
            self.emit("store", idx)
        elif rtag == "abox":
            self.load_atom(rhs[1])
            self.emit("prim", "box", 1)
            self.emit("store", idx)
        elif rtag == "aunbox":
            self.load_atom(rhs[1])
            self.emit("prim", "unbox", 1)
            self.emit("store", idx)
        elif rtag == "asetbox":
            self.load_atom(rhs[1])
            self.load_atom(rhs[2])
            self.emit("prim", "set-box!", 2)
            self.emit("store", idx)
        elif rtag == "acopy":
            self.load_atom(rhs[1])
            self.emit("store", idx)
        else:
            raise AssertionError("bad rhs %r" % (rtag,))
        self.bind(name, idx, body)

    def aif(self, t):
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

    def atry(self, t):
        """('atry', name, bterm, hatom, cont): name := try bterm catch -> h(exc)."""
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
        # TOS holds the caught exception payload
        self.emit("store", exc_i)
        self.load_atom(hatom)
        self.emit("load", exc_i)
        self.emit("call", 1)
        self.emit("store", val_i)
        self.code[j_end] = ("jmp", len(self.code))
        self.bind(name, val_i, cont)
