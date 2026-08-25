"""Benchmark + verification harness.

  python -m sc.bench                 # full report
  python -m sc.bench --quick         # fewer reps
"""
from __future__ import annotations

import argparse
import glob
import os
import statistics
import sys
import time

from .compiler import compile_source, compile_unspecialized, CompileOptions
from .vm import run as vm_run
from .driver import Driver, Options as DriverOptions, Bail
from .sexp import parse_all
from .lang import desugar_top
from .front import closure_convert
from .anf import anf_convert
from .bigstack import run_program_bigstack
from sc.decompile import program_to_source


def norm(v, depth=8):
    from .semantics import Pair, Box, Closure, Sym
    if depth <= 0:
        return "..."
    if isinstance(v, Pair):
        return ("p", norm(v.hd, depth - 1), norm(v.tl, depth - 1))
    if isinstance(v, Box):
        return "#box"
    if isinstance(v, Closure) or hasattr(v, "fid"):
        return "#proc"
    if v is None:
        return "()"
    if isinstance(v, Sym):
        return ("sym", v.name)
    if isinstance(v, tuple) and len(v) == 2 and v[0] == "err":
        return v
    return v


def outcome(o):
    return (tuple(o["out"]), o["status"], norm(o["value"]))


def time_runs(bp, reps=5, fuel=200_000_000):
    ts = []
    for _ in range(reps):
        t0 = time.perf_counter()
        r = vm_run(bp, fuel=fuel)
        ts.append(time.perf_counter() - t0)
        if r["status"] == "timeout":
            return None, r
    return min(ts), r


def bench_table(reps=5):
    files = sorted(glob.glob(os.path.join(
        os.path.dirname(__file__), "..", "benchmarks", "*.sc")))
    rows = []
    for f in files:
        name = os.path.basename(f)
        src = open(f).read()
        try:
            bu = compile_unspecialized(src)
            bo = compile_source(src)
        except Exception as e:
            rows.append((name, None, None, None, None, None, "compile-err"))
            continue
        rb = vm_run(bu)
        ro = vm_run(bo)
        agree = outcome(rb) == outcome(ro)
        tb, _ = time_runs(bu, reps)
        to, _ = time_runs(bo, reps)
        sbu = bu.total_instructions()
        sbo = bo.total_instructions()
        speed = tb / to if (tb and to) else None
        rows.append((name, tb, to, speed, sbu, sbo,
                     "ok" if agree else "DIVERGE"))
    print("%-26s %10s %10s %8s %8s %8s %s" %
          ("benchmark", "t_base", "t_opt", "speedup", "size_b", "size_o",
           "agree"))
    for name, tb, to, sp, sb, so, ok in rows:
        fmt = lambda t: ("%9.4fs" % t) if t else ("      n/a")
        spd = ("%7.2fx" % sp) if sp else "     n/a"
        print("%-26s %10s %10s %8s %8d %8d %s" %
              (name, fmt(tb), fmt(to), spd, sb, so, ok))
    return rows


def alloc_counts(f, reps=1):
    """cons/box allocation counts base vs optimized."""
    src = open(f).read()
    bu = compile_unspecialized(src)
    bo = compile_source(src)
    rb = vm_run(bu)
    ro = vm_run(bo)
    return rb["cons_alloc"], ro["cons_alloc"], rb["box_alloc"], ro["box_alloc"], \
        outcome(rb) == outcome(ro)


def deforestation_report():
    files = sorted(glob.glob(os.path.join(
        os.path.dirname(__file__), "..", "benchmarks", "*pipeline*.sc")))
    files += sorted(glob.glob(os.path.join(
        os.path.dirname(__file__), "..", "benchmarks", "*foldmap*.sc")))
    print("\n== deforestation: intermediate pair allocations ==")
    print("%-30s %12s %12s %10s" % ("benchmark", "pairs_base", "pairs_opt",
                                    "ratio"))
    for f in files:
        cb, co, bb, bo2, ok = alloc_counts(f)
        ratio = ("%.4f" % (co / cb)) if cb else "n/a"
        print("%-30s %12d %12d %10s %s" %
              (os.path.basename(f), cb, co, ratio,
               "" if ok else "DIVERGE"))


def idempotence_report():
    files = sorted(glob.glob(os.path.join(
        os.path.dirname(__file__), "..", "benchmarks", "*.sc")))
    print("\n== idempotence: optimizing optimized output ==")
    print("%-26s %8s %8s %10s %s" % ("benchmark", "size1", "size2",
                                     "delta", "agree"))
    for f in files:
        name = os.path.basename(f)
        src = open(f).read()
        try:
            b1 = compile_source(src)
            r1 = vm_run(b1)
            # decompile residual IR and recompile through the full pipeline
            prog = desugar_top(parse_all(src))
            ir = anf_convert(closure_convert(prog))
            drv = Driver(ir)
            try:
                residual = drv.run()
            except Bail:
                residual = {"funds": {}, "main": ir["main"]}
            unified = {"funds": {**ir["funds"], **residual["funds"]},
                       "main": residual["main"]}
            from .compiler import dce
            unified = dce(unified)
            src2 = program_to_source(unified)
            b2 = compile_source(src2)
            r2 = vm_run(b2)
            s1, s2 = b1.total_instructions(), b2.total_instructions()
            delta = abs(s2 - s1) / max(1, s1)
            agree = outcome(r1) == outcome(r2)
            print("%-26s %8d %8d %9.1f%% %s" %
                  (name, s1, s2, delta * 100, "ok" if agree else "DIVERGE"))
        except Exception as e:
            print("%-26s err %s" % (name, repr(e)[:60]))


def explosion_curve():
    print("\n== code-explosion cutoff sweep (b17_explosion.sc family) ==")
    f = os.path.join(os.path.dirname(__file__), "..", "benchmarks",
                     "b17_explosion.sc")
    src = open(f).read()
    print("%10s %10s %10s %8s" % ("factor K", "size", "vs-base", "time_s"))
    bu = compile_unspecialized(src)
    sbase = bu.total_instructions()
    for k in [1, 2, 4, 8, 16, 32]:
        opts = CompileOptions()
        opts.expand_factor = k
        t0 = time.perf_counter()
        bp = compile_source(src, opts)
        dt = time.perf_counter() - t0
        r = vm_run(bp)
        print("%10.0f %10d %10.2f %8.2f" %
              (k, bp.total_instructions(),
               bp.total_instructions() / max(1, sbase), dt))


def whistle_stress():
    """A family whose driving tree grows without bound.

    sum-acc has a linear accumulator; with the whistle disabled the driver
    unfolds until budgets stop it (still terminating, still correct, but
    producing bail-outs instead of a folded loop). We measure unfold counts.
    """
    print("\n== whistle stress: driving growth with vs without HE ==")
    src = """
(define (sum-acc n acc) (if (= n 0) acc (sum-acc (- n 1) (+ acc n))))
(sum-acc 400 0)
"""
    prog = desugar_top(parse_all(src))
    ir = anf_convert(closure_convert(prog))

    d1 = Driver(ir)
    res1 = d1.run()

    # disable the whistle: embed always False
    import sc.he as he_mod
    orig_embed = he_mod.embed
    he_mod.embed = lambda *a, **k: False
    try:
        d2 = Driver(ir)
        res2 = d2.run()
    finally:
        he_mod.embed = orig_embed

    print("with HE : unfolds=%3d folds=%2d gens=%2d resfuncs=%d" %
          (d1.stats["unfolded"], d1.stats["folded"],
           d1.stats["generalized"], len(d1.res_funds)))
    print("no HE   : unfolds=%3d folds=%2d gens=%2d resfuncs=%d" %
          (d2.stats["unfolded"], d2.stats["folded"],
           d2.stats["generalized"], len(d2.res_funds)))
    print("growth trend: no-HE unfold count grows ~linearly with n "
          "(budget-bounded); with HE it is capped by generalization.")
    # correctness of both residuals
    from .bc import compile_ir
    from .vm import run as vr
    u1 = {"funds": {**ir["funds"], **res1["funds"]}, "main": res1["main"]}
    u2 = {"funds": {**ir["funds"], **res2["funds"]}, "main": res2["main"]}
    print("values:", vr(compile_ir(u1))["value"], vr(compile_ir(u2))["value"])


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--skip-idempotence", action="store_true")
    args = ap.parse_args(argv)
    reps = 3 if args.quick else 7
    bench_table(reps)
    deforestation_report()
    explosion_curve()
    whistle_stress()
    if not args.skip_idempotence:
        idempotence_report()


if __name__ == "__main__":
    main()
