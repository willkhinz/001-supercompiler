"""Compiler orchestration: source -> bytecode, with optional supercompilation."""
from __future__ import annotations

import time

from .sexp import parse_all
from .lang import desugar_top, LangError
from .front import closure_convert
from .anf import anf_convert
from .driver import (Driver, Options as DriverOptions, Bail,
                     PureEvalAbort)
from .bc import compile_ir


class CompileOptions:
    def __init__(self):
        self.specialize = True
        self.expand_factor = 16.0
        self.min_repeat = 2
        self.max_funcs = 4000
        self.max_history = 60
        self.no_specialize = set()
        self.per_func_budget = {}
        self.pure_eval_steps = 20000

    def apply_declares(self, forms):
        """Consume (declare ...) forms; returns remaining forms."""
        rest = []
        for f in forms:
            if isinstance(f, list) and f and isinstance(f[0], tuple) \
                    and f[0][0] == "sym" and f[0][1] == "declare":
                self._declare(f[1:])
            else:
                rest.append(f)
        return rest

    def _declare(self, args):
        if not args:
            return
        kind = args[0]
        kname = kind[1] if isinstance(kind, tuple) else str(kind)
        if kname == "no-specialize" and len(args) >= 2:
            self.no_specialize.add(args[1][1])
        elif kname == "specialize-aggressive" and len(args) >= 2:
            nm = args[1][1]
            self.per_func_budget[nm] = float(
                args[2][1]) if len(args) > 2 else 1e9
        elif kname == "budget" and len(args) >= 3:
            self.per_func_budget[args[1][1]] = float(args[2][1])
        elif kname == "expand-factor" and len(args) >= 2:
            self.expand_factor = float(args[1][1])
        elif kname == "min-repeat" and len(args) >= 2:
            self.min_repeat = int(args[1][1])


def _refs(t, acc):
    stack = [t]
    while stack:
        x = stack.pop()
        if not isinstance(x, tuple):
            continue
        if x and x[0] in ("adirect", "rdirect"):
            acc.add(x[1])
        if x and x[0] in ("amkclo", "rmkclo"):
            acc.add(x[1])
        stack.extend(x[1:])


def dce(irprog):
    """Drop unreachable funds (originals only referenced by bail paths stay)."""
    reachable = set()
    work = [irprog["main"]]
    while work:
        t = work.pop()
        acc = set()
        _refs(t, acc)
        new = acc - reachable
        reachable |= acc
        for fid in new:
            if fid in irprog["funds"]:
                work.append(irprog["funds"][fid][1])
    kept = {k: v for k, v in irprog["funds"].items() if k in reachable}
    return {"funds": kept, "main": irprog["main"]}


def compile_source(src: str, opts: CompileOptions | None = None,
                   collect_stats=False):
    opts = opts or CompileOptions()
    t0 = time.time()
    forms = parse_all(src)
    forms = opts.apply_declares(forms)
    prog = desugar_top(forms)
    t1 = time.time()
    lifted = closure_convert(prog)
    ir = anf_convert(lifted)
    t2 = time.time()

    stats = {"src_bytes": len(src)}
    if opts.specialize:
        # Phase 1: bounded pure static evaluation -- if the whole program
        # evaluates concretely within the step budget, intermediates never
        # materialize (zero allocation fusion).
        pe = Driver(ir, DriverOptions(pure_eval_steps=opts.pure_eval_steps))
        try:
            res_pe = pe.run()
            stats["phase1"] = "static-eval"
            t3 = time.time()
            unified_pe = dce({"funds": {**ir["funds"], **res_pe["funds"]},
                              "main": res_pe["main"]})
            bp = compile_ir(unified_pe)
            t4 = time.time()
            stats.update({"anf_funds": len(ir["funds"]),
                          "final_funds": len(unified_pe["funds"]),
                          "code_size": bp.total_instructions(),
                          "t_front": t1 - t0, "t_anf": t2 - t1,
                          "t_drive": t3 - t2, "t_bc": t4 - t3})
            return bp
        except (PureEvalAbort, Bail):
            stats["phase1"] = "abort"

    if opts.specialize:
        dopts = DriverOptions(
            expand_factor=opts.expand_factor,
            min_repeat=opts.min_repeat,
            max_funcs=opts.max_funcs,
            max_history=opts.max_history,
            no_specialize=opts.no_specialize,
            per_func_budget=opts.per_func_budget,
        )
        drv = Driver(ir, dopts)
        try:
            residual = drv.run()
        except Bail:
            # safety net: emit unspecialized program
            stats["bail_total"] = True
            residual = {"funds": {}, "main": ir["main"]}
        stats.update(drv.stats)
        stats["residual_funcs"] = len(residual["funds"])
        unified = {"funds": {**ir["funds"], **residual["funds"]},
                   "main": residual["main"]}
    else:
        unified = ir
    t3 = time.time()

    unified = dce(unified)
    bp = compile_ir(unified)
    t4 = time.time()

    stats.update({
        "anf_funds": len(ir["funds"]),
        "final_funds": len(unified["funds"]),
        "code_size": bp.total_instructions(),
        "t_front": t1 - t0, "t_anf": t2 - t1, "t_drive": t3 - t2,
        "t_bc": t4 - t3,
    })
    if collect_stats:
        return bp, stats
    return bp


def compile_unspecialized(src: str):
    opts = CompileOptions()
    opts.specialize = False
    return compile_source(src, opts)


def anf_size_of_program(src: str):
    forms = parse_all(src)
    prog = desugar_top(forms)
    lifted = closure_convert(prog)
    ir = anf_convert(lifted)
    n = 0
    from .driver import _anf_size
    for _, (_, body) in ir["funds"].items():
        n += _anf_size(body)
    return n + _anf_size(ir["main"])
