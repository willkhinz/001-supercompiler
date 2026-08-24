"""Stack bytecode VM: iterative (no Python recursion), tail calls,
first-class closures, exceptions with cross-frame unwinding, step fuel,
allocation stats.
"""
from __future__ import annotations

from .semantics import Box, Pair, ScmError, format_value, prim


class VClo:
    __slots__ = ("fid", "frees")

    def __init__(self, fid, frees):
        self.fid = fid
        self.frees = frees


class Frame:
    __slots__ = ("code", "pc", "stack", "locals", "catches")

    def __init__(self, code, locals_):
        self.code = code
        self.pc = 0
        self.stack = []
        self.locals = locals_
        self.catches = []


class _Exit(Exception):
    def __init__(self, status, value):
        self.status = status
        self.value = value


def run(prog: dict, fuel=100_000_000):
    """prog: BytecodeProgram -> outcome dict with stats."""
    funds = prog.funds
    out = []
    steps = 0
    cons_alloc = 0
    box_alloc = 0

    frames = [Frame(prog.main.code, [None] * prog.main.nlocals)]
    f = frames[0]

    try:
        while True:
            if steps >= fuel:
                raise _Exit("timeout", None)
            steps += 1
            ins = f.code[f.pc]
            op = ins[0]
            f.pc += 1

            if op == "const":
                f.stack.append(ins[1])

            elif op == "load":
                f.stack.append(f.locals[ins[1]])

            elif op == "store":
                f.locals[ins[1]] = f.stack.pop()

            elif op == "prim":
                name = ins[1]
                n = ins[2]
                st = f.stack
                if n:
                    args = st[-n:]
                    del st[-n:]
                else:
                    args = []
                if name == "print":
                    out.append(format_value(args[0]))
                    st.append(None)
                elif name == "cons":
                    cons_alloc += 1
                    st.append(Pair(args[0], args[1]))
                elif name == "box":
                    box_alloc += 1
                    st.append(Box(args[0]))
                else:
                    try:
                        st.append(prim(name, args))
                    except ScmError as e:
                        f = _raise(frames, ("err", e.msg))

            elif op in ("call", "callt"):
                n = ins[1]
                st = f.stack
                fn = st[-n - 1]
                args = st[-n:]
                del st[-n - 1:]
                if not isinstance(fn, VClo):
                    f = _raise(frames, ("err", "err:call-of-non-closure"))
                    continue
                fund = funds.get(fn.fid)
                nargs_total = len(args) + len(fn.frees)
                if fund is None or nargs_total != fund.nparams:
                    f = _raise(frames, ("err", "err:bad-arity"))
                    continue
                nloc = list(fn.frees) + list(args)
                if op == "callt":
                    _tail(f, fund, nloc)
                else:
                    f = _enter(frames, fund, nloc)

            elif op in ("calld", "calldt"):
                fid = ins[1]
                n = ins[2]
                st = f.stack
                args = st[-n:]
                del st[-n:]
                fund = funds[fid]
                if n != fund.nparams:
                    f = _raise(frames, ("err", "err:bad-arity"))
                    continue
                nloc = list(args)
                if op == "calldt":
                    _tail(f, fund, nloc)
                else:
                    f = _enter(frames, fund, nloc)

            elif op == "ret":
                v = f.stack.pop()
                frames.pop()
                f = frames[-1]
                f.stack.append(v)

            elif op == "jmp":
                f.pc = ins[1]

            elif op == "jiff":
                v = f.stack.pop()
                if not isinstance(v, bool):
                    f = _raise(frames, ("err", "err:if-condition-not-bool"))
                    continue
                if not v:
                    f.pc = ins[1]

            elif op == "clo":
                fid = ins[1]
                k = ins[2]
                st = f.stack
                frees = tuple(st[-k:]) if k else ()
                if k:
                    del st[-k:]
                st.append(VClo(fid, frees))

            elif op == "try":
                f.catches.append((ins[1], len(f.stack)))

            elif op == "endtry":
                f.catches.pop()

            elif op == "raise":
                v = f.stack.pop()
                f = _raise(frames, v)

            elif op == "halt":
                raise _Exit("ok", f.stack.pop() if f.stack else None)

            else:
                raise AssertionError("bad opcode %r" % (op,))

    except _Exit as e:
        status, result = e.status, e.value

    return {
        "out": out,
        "status": status,
        "value": result,
        "steps": steps,
        "cons_alloc": cons_alloc,
        "box_alloc": box_alloc,
    }


def _enter(frames, fund, locals_):
    frames.append(Frame(fund.code, locals_ + [None] * max(0, fund.nlocals - len(locals_))))
    return frames[-1]


def _tail(f, fund, locals_):
    f.locals = locals_ + [None] * max(0, fund.nlocals - len(locals_))
    del f.stack[:]
    f.catches.clear()
    f.pc = 0
    f.code = fund.code


def _raise(frames, payload):
    """Unwind to nearest catch; raises _Exit when uncaught."""
    while True:
        f = frames[-1]
        if f.catches:
            hpc, slen = f.catches.pop()
            del f.stack[slen:]
            f.pc = hpc
            f.stack.append(payload)
            return f
        if len(frames) == 1:
            raise _Exit("exc", payload)
        frames.pop()
