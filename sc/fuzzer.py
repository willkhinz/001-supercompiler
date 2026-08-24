"""Differential fuzzer driver: run N random programs through
ref-interpreter, unoptimized VM, supercompiled VM; compare everything.

Usage:
    python -m sc.fuzzer --n 50000 --seed 0 [--workers 8] [--outdir failures]
"""
from __future__ import annotations

import argparse
import os
import sys
import time
import traceback

from .fuzz_gen import gen_program, to_source, compare
from .sexp import parse_all
from .lang import desugar_top
from .compiler import compile_source, CompileOptions, compile_unspecialized
from .vm import run as vm_run


def check_one(seed, opts: CompileOptions | None = None):
    """Returns (problems, meta). problems empty == pass."""
    forms = gen_program(seed)
    src = to_source(forms)
    try:
        prog = desugar_top(parse_all(src))
    except Exception as e:
        return None, {"seed": seed, "skip": "gen:%s" % e}
    from .bigstack import run_program_bigstack
    try:
        ref = run_program_bigstack(prog)
    except Exception:
        return None, {"seed": seed, "skip": "ref-crash"}
    if ref["status"] == "timeout":
        return None, {"seed": seed, "skip": "ref-timeout"}
    try:
        bu = compile_unspecialized(src)
        base = vm_run(bu)
        bp, stats = compile_source(src, opts or CompileOptions(),
                                   collect_stats=True)
        opt = vm_run(bp)
    except Exception as e:
        return [("compiler-crash", repr(e), traceback.format_exc())], \
            {"seed": seed}
    if base["status"] == "timeout" or opt["status"] == "timeout":
        return [("timeout", base["status"], opt["status"])], {"seed": seed}
    problems = compare(ref, base, opt)
    return problems, {"seed": seed, "stats": stats}


def _worker(args):
    seed, outdir = args
    try:
        problems, meta = check_one(seed)
    except Exception as e:
        problems = [("harness-crash", repr(e), traceback.format_exc())]
        meta = {"seed": seed}
    if problems and outdir:
        os.makedirs(outdir, exist_ok=True)
        src = to_source(gen_program(seed))
        with open(os.path.join(outdir, "fail_%d.sc" % seed), "w") as f:
            f.write(src)
        with open(os.path.join(outdir, "fail_%d.txt" % seed), "w") as f:
            for p in problems:
                f.write(repr(p) + "\n\n")
    return seed, problems


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--outdir", default="failures")
    args = ap.parse_args(argv)

    t0 = time.time()
    fails = 0
    skipped = 0
    done = 0
    seeds = range(args.seed, args.seed + args.n)

    if args.workers <= 1:
        for s in seeds:
            _, problems = _worker((s, None))
            if problems is None:
                skipped += 1
            elif problems:
                fails += 1
                print("FAIL seed", s, problems[0][0])
                if fails <= 3:
                    for p in problems:
                        print("  ", str(p)[:500])
            done += 1
            if done % 5000 == 0:
                el = time.time() - t0
                print("... %d done, %d fails, %.1fs" % (done, fails, el),
                      flush=True)
    else:
        import multiprocessing as mp
        with mp.Pool(args.workers) as pool:
            for i, (s, problems) in enumerate(
                    pool.imap_unordered(_worker,
                                        [(s, None) for s in seeds],
                                        chunksize=200)):
                if problems is None:
                    skipped += 1
                elif problems:
                    fails += 1
                    print("FAIL seed", s, problems[0][0], flush=True)
                    if fails <= 5:
                        for p in problems:
                            print("  ", str(p)[:600])
                done += 1
                if done % 10000 == 0:
                    el = time.time() - t0
                    rate = done / el
                    print("... %d done, %d fails, %.0f/s" %
                          (done, fails, rate), flush=True)

    el = time.time() - t0
    print("=" * 60)
    print("programs: %d  failed: %d  skipped: %d  elapsed: %.1fs"
          % (args.n, fails, skipped, el))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
