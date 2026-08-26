# sc — a whole-program supercompiler for SC-Lang

`sc` is a whole-program supercompiler (aggressive offline partial evaluator) for **SC-Lang**, a strict Scheme subset with first-class closures, immutable pairs, mutable boxes, and exceptions. It parses a whole program, lambda-lifts and ANF-normalizes it, then *drives* it symbolically — unfolding calls, evaluating what it can, splitting on unknown conditions, detecting infinite unfolding with a homeomorphic-embedding whistle, generalizing loop patterns into parameterized residual functions, and folding recursive call sites back onto them — before emitting compact bytecode for an iterative stack VM. Its defining property is that all of this aggression is behavior-preserving: every optimization run is checked against two independent oracles (a tree-walking reference interpreter and the unoptimized VM), comparing printed output, termination status, final value/exception payload, and the exact sequence of box mutations.

## Features

**Language front end**
- S-expression reader (`sc/sexp.py`): ints, `#t`/`#f`, symbols, `'` quote sugar, `[...]` brackets, comments, string literals.
- Desugarer (`sc/lang.py`): `define` (both forms), `lambda`, `if`, `begin`, `let`, `let*`, `letrec`, named `let`, `cond`, `and`, `or`, `when`, `unless`, `list`, `quote`, `box`/`unbox`/`set-box!`, `raise`/`try`. Primitives are arity-checked at desugar time; primitives used as values are eta-expanded into closures.
- Shared value semantics (`sc/semantics.py`) used by *both* executors so primitive behavior, error identities (`err:division-by-zero`, `err:car-of-non-pair`, …), and printing cannot drift apart. Primitives are classified pure / effectful (`print`, `set-box!`) / dynamic (`unbox`).

**Two independent executors**
- Reference interpreter (`sc/refinterp.py`): tree-walking evaluator on the desugared AST, sharing only value semantics — the ground-truth oracle.
- Bytecode VM (`sc/vm.py`): iterative (no Python recursion), proper tail calls, first-class closures, exceptions with cross-frame unwinding, step fuel, and allocation counters (`cons_alloc`, `box_alloc`).
- `sc/bigstack.py`: runs deep-but-finite programs through the recursive reference interpreter on a thread with a large stack.

**The optimizer**
- Closure conversion / lambda lifting (`sc/front.py`) with correct mutual recursion: every function reference becomes `(mkclo fid frees)`, plus a purity analysis of top-level defs so value-capturing ("impure") defs keep source-order semantics.
- ANF normalization (`sc/front.py`, exposed via `sc/anf.py`) with globally unique binders.
- Whole-program supercompiler (`sc/driver.py`): driving over a symbolic value domain (static scalars, symbolic conses and closures, dynamic runtime values, case-splits), static evaluation of pure primitives including symbolic `cons`/`car`/`cdr`, branch pruning only on statically-known booleans, residual merging of both branches otherwise.
- Homeomorphic-embedding whistle (`sc/he.py`) with the HE3 divisibility guard on integers (`i ◁ j` iff `i = j` or signs match and `|j| ≥ 2·max(|i|,1)`), countdown-fuel slot masking, memoized embedding, and per-unfold alpha-renaming to prevent variable capture.
- Generalization + folding: common-loop-shape generalization into fresh residual funds, exact-partition fold-table matching, pattern deduplication via memoized fixed-slot keys.
- Cost model bounding code growth: per-function expansion budgets (`expand_factor`, per-func `budget`/`specialize-aggressive` declares, `no-specialize` opt-outs), history cap, function cap; graceful `Bail` back to the unspecialized program.
- Phase-1 bounded pure static evaluation: if the whole program evaluates within a step budget, the residual is a constant.
- Dead-code elimination over the unified fund graph (`sc/compiler.py:dce`).
- Bytecode compiler (`sc/bc.py`) and IR-to-source decompiler (`sc/decompile.py`) for residual inspection.

**Verification harness**
- Differential fuzzer (`sc/fuzzer.py`, `sc/fuzz_gen.py`): seeded generator of well-typed programs with recursion, boxes, `try`/`raise`, and higher-order calls; triple-oracle comparison (reference vs base VM vs supercompiled VM) covering output order, status, normalized value, and mutation traces; multiprocessing workers; failing seeds written to `failures/`.
- Benchmark harness (`sc/bench.py`): 20-program suite with speedup/code-size tables, deforestation allocation counts, code-explosion sweep, whistle stress test, and an idempotence probe.

## Architecture

```
source.sc ──sexp──▶ forms ──lang──▶ AST ──front──▶ lifted funds ──anf──▶ ANF IR
                                                                        │
                                              ┌─────────────────────────┤
                                              ▼ (phase 1: pure eval)    ▼ (phase 2: full drive)
                                          constant residual         residual r-terms + g-funds
                                              └────────────┬────────────┘
                                                           ▼ dce + bc.compile_ir
                                                     BytecodeProgram ──vm.run──▶ outcome
```

Module responsibilities:

| Module | Role |
|---|---|
| `sc/sexp.py` | reader/printer; symbols are `("sym", name)` nodes |
| `sc/lang.py` | tagged-tuple AST (`('const',v) ('var',n) ('lam',…) ('app',…) …`), desugarer, `free_vars`, `size_of` |
| `sc/semantics.py` | `Sym` (interned), `Pair`, `Box`, `Closure`, `ScmError`, prim application, formatting, structural equality |
| `sc/refinterp.py` | independent oracle interpreter (env-copying closures, fuel counter) |
| `sc/bigstack.py` | large-stack thread runner for the oracle |
| `sc/front.py` | closure conversion (`closure_convert`) + ANF (`Anfer`) |
| `sc/anf.py` | one-line wrapper around `Anfer` |
| `sc/he.py` | homeomorphic embedding on configuration trees, memoized, depth-capped |
| `sc/driver.py` | the supercompiler: symbolic domain, driving, whistle, generalization, folding, residual emission |
| `sc/compiler.py` | orchestration (`compile_source`), `CompileOptions` + `(declare …)` handling, DCE, phase selection |
| `sc/bc.py` | IR → linear bytecode (`const/load/store/prim/call/callt/calld/calldt/ret/jmp/jiff/clo/try/endtry/raise/halt`) |
| `sc/vm.py` | stack VM: explicit frames, catch stacks per frame, tail-call reuse, `_raise` unwind |
| `sc/decompile.py` | unified IR → SC-Lang source |
| `sc/bench.py`, `sc/fuzzer.py`, `sc/fuzz_gen.py` | measurement and differential-testing harness |

Key data structures and algorithms:

- **AST**: immutable tagged tuples throughout, so trees are cheap to share and hash by identity in caches.
- **Programs**: desugared `{'items': [('def'|'val', name, rhs)…], 'body': expr}` → lifted/ANF `{'funds': {fid: (params, body)}, 'main': term}`. ANF atoms are `('acon', v)`/`('avar', n)`; terms are `ahalt/araise/alet/aif/atry`; residual terms add `r*` variants plus value-producing rhs kinds (`rsub`, `rifv`, `rtry`).
- **Symbolic values** in the driver: scalars; `('scons', h, t)` symbolic pairs; `('sclo', fid, frees)` symbolic closures (created only when all captured values are context-free); `('dyn', name)` opaque runtime values; `('case', cond, then, else)` pending conditionals. Pure-primitive evaluation (`eval_sym_prim`) mirrors `semantics.prim` exactly over this extended domain.
- **Configurations** (`Cfg`): a fund body rendered as a tree whose variable references point into an ordered slot vector of symbolic values — this is the object the whistle compares. Embedding an ancestor config into the current one means "we have seen this shape before, deeper": blow the whistle.
- **Whistle**: `he.embed` implements divisibility-guarded integer comparison (blocks immediate-successor loops like `n → n−1` from being called growth, catches geometric growth), exact coupling of variable slots, bounded tail-digging for cons spines, and truncation that biases toward whistling (termination-safe). Slots holding strictly-decreasing concrete ints relative to the same-fid ancestor are masked as self-terminating countdown fuel; a hit explained purely by masked slots does *not* whistle.
- **Generalization**: on a confirmed whistle, slots equal-and-context-free on both sides are frozen into the pattern, differing extractable slots become parameters `q0…qn`, and the pattern body is driven once and cached (`pattern_memo`); later configurations matching the partition fold onto it via direct calls to the generalized fund (`fold_table`).
- **Soundness rules** (stated in `driver.py`, enforced structurally): **E1** boxes are opaque — box/unbox/set-box! always residualize in ANF order; **E2** pairs are immutable — `cons` computes symbolically, `car`/`cdr` deconstruct purely; **E3** effectful prims are emitted exactly once, never evaluated statically; **E4** branch pruning only on statically-known booleans, otherwise drive both sides and merge residually; **E5** a static result implies its effects were already emitted; **E6** static exception propagation only rewrites a definite raise into its lexically enclosing driven `try`.
- **Cost model**: each unfolded fund accrues node-size against `spent[fid] ≤ expand_factor × orig_size(fid)` (overridable per-function); exceeding budget switches that fund to bail-out direct calls to the original body — correct, just less specialized. History/function caps trigger `Bail`, which emits the unspecialized program.

## Requirements

- **Python 3** — verified on **CPython 3.13.5** (macOS). Earlier 3.x versions: unmeasured/untested.
- **No third-party dependencies** — standard library only (`argparse`, `glob`, `os`, `random`, `sys`, `time`, `threading`, `multiprocessing`, `statistics`).
- No build step; the package runs in place from the repository root.

## Build & Setup

There is nothing to build. All commands below were executed and passed in this session from the repository root:

```sh
# sanity: import the package and compile+run a program end-to-end
python3 - <<'EOF'
from sc.compiler import compile_source
from sc.vm import run
bp = compile_source("(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib 16)")
print(bp.total_instructions())          # -> 2
print(run(bp)["value"])                 # -> 987
EOF
# 2
# 987
```

## Usage

**Command-line entry points**

```sh
python tests/test_smoke.py        # 16 front-end/VM agreement checks
python tests/test_super.py        # 9 end-to-end specialization cases vs both oracles
python -m sc.bench [--quick]      # benchmark suite + reports   (--quick uses 3 reps instead of 7)
python -m sc.fuzzer --n 10000 --seed 0 [--workers 8] [--outdir failures]
```

**Library use**

```python
from sc.compiler import compile_source, CompileOptions
from sc.vm import run

src = """
(declare (no-specialize sum))     ; leave one function untouched
(declare (expand-factor 8))       ; tighten the global growth budget
(define (sum n acc) (if (= n 0) acc (sum (- n 1) (+ acc n))))
(sum 100 0)
"""
bp = compile_source(src)                    # full pipeline incl. supercompilation
r = run(bp)                                 # r["status"]=="ok", r["value"]==5050
# other options: CompileOptions().per_func_budget["g"]=N,
#                opts.pure_eval_steps, opts.min_repeat, opts.max_funcs ...
```

Supported `(declare …)` forms (consumed by `CompileOptions.apply_declares`): `no-specialize`, `specialize-aggressive`, `budget`, `expand-factor`, `min-repeat`.

**Language surface** (see `tests/test_smoke.py` for working snippets): closures and currying-style makers, mutual recursion, named `let` loops, deep tail recursion (50 000 iterations verified), lists built from `cons`/`quote`, boxed mutable state with ordered effects, `try`/`raise` with arbitrary payloads (including nested re-raise), and runtime errors raised as catchable `("err", msg)` payloads.

**Inspecting residuals**

```python
from sc.decompile import program_to_source
from sc.sexp import parse_all
from sc.lang import desugar_top
from sc.front import closure_convert
from sc.anf import anf_convert
from sc.driver import Driver

prog = desugar_top(parse_all(src))
ir = anf_convert(closure_convert(prog))
residual = Driver(ir).run()
print(residual["funds"].keys(), residual["main"])   # raw residual IR
```

## Running Tests & Benchmarks

Exact commands executed in this session:

```sh
python3 tests/test_smoke.py
python3 tests/test_super.py
python3 -m sc.bench            # full suite, 7 reps
python3 -m sc.bench --quick    # 3 reps (also run once, results consistent)
python3 -m sc.fuzzer --n 300 --seed 0
python3 -m sc.fuzzer --n 2000 --seed 0
```

All tests exit 0; `sc.bench` prints four reports (table, deforestation, explosion sweep, whistle stress, then idempotence); `sc.fuzzer` exits 0 when no seed diverges.

## Measured Results

All numbers below were produced in this session on CPython 3.13.5, macOS; timings are wall-clock min-of-N from `sc.bench`/`test_super` on one machine and will vary elsewhere. Anything not measured here is labeled **unmeasured**.

### Correctness

- `tests/test_smoke.py`: **16/16 programs agree** between reference interpreter and unoptimized VM (arith, conditionals, recursion, lists, boxes, effect ordering, exceptions incl. static propagation, closures, mutual recursion, named let, 50k-deep tail recursion, error catching, shadowing, higher-order capture, nested try).
- `tests/test_super.py`: **9/9 cases** where reference == unoptimized == supercompiled output.
- `python3 -m sc.fuzzer --n 2000 --seed 0`: **2000 programs, 0 failures, 0 skipped, 2.1 s** (triple-oracle incl. mutation traces). A 300-seed spot run was likewise 0 failures in 0.3 s.
- `python3 -m sc.bench`: **20/20 benchmarks `agree`** between base and optimized VM outcomes.

### Specialization quality (`tests/test_super.py`, sizes in bytecode instructions)

| case | size base→opt | time base→opt | speedup |
|---|---|---|---|
| fib | 45→2 | 0.0235 s→~1 µs | ~23 481× |
| pipeline | 216→37 | 5.6e-4 s→4.4e-6 s | ~127× |
| power | 37→2 | 3.5e-5 s→7.9e-7 s | ~44× |
| ackermann_small | 68→2 | 1.4e-4 s→8.8e-7 s | ~162× |
| boxes_effects | 56→60 (+7%) | ≈equal | ~1.02× |
| exceptions_flow | 81→20 | 1.4e-5 s→2.8e-6 s | ~5.1× |
| closures_pipeline | 48→2 | 9.0e-6 s→8.3e-7 s | ~10.8× |
| mutual_recursion | 54→2 | 1.25e-4 s→8.8e-7 s | ~143× |
| interpreter_specialization | 236→1035 (**4.39× larger**) | 3.7e-5 s→2.0e-5 s | ~1.88× |

Fully-static programs collapse to a constant residual: e.g. `fib(16)` compiles to a 2-instruction program returning `987` in 2 VM steps (verified directly above).

### Full benchmark table (`python3 -m sc.bench`, 7 reps)

| benchmark | t_base | t_opt | speedup | size_b | size_o | agree |
|---|---|---|---|---|---|---|
| b01_fib | 0.0087s | <0.00005s | 10985× | 45 | 2 | ok |
| b02_pipeline | 0.0027s | 0.0025s | 1.09× | 216 | 6200 | ok |
| b03_sumacc | 0.0128s | 0.0130s | 0.98× | 37 | 154 | ok |
| b04_ackermann | 0.0002s | <0.00005s | 286× | 68 | 2 | ok |
| b05_power | 0.0001s | <0.00005s | 133× | 48 | 2 | ok |
| b06_quicksort | 0.0024s | <0.00005s | 3048× | 361 | 2 | ok |
| b07_mutual | 0.0020s | 0.0018s | 1.11× | 68 | 182 | ok |
| b08_boxes_counter | 0.0137s | 0.0139s | 0.99× | 48 | 48 | ok |
| b09_try_heavy | 0.0060s | 0.0059s | 1.00× | 49 | 1006 | ok |
| b10_interpreter | 0.0001s | <0.00005s | 101× | 264 | 2 | ok |
| b11_tailcount | 0.0192s | 0.0193s | 1.00× | 37 | 154 | ok |
| b12_collatz | 0.0005s | 0.0003s | 1.79× | 64 | 421 | ok |
| b13_gcd_list | 0.0006s | 0.0004s | 1.55× | 96 | 1858 | ok |
| b14_mergesort_len | 0.0009s | <0.00005s | 1246× | 297 | 2 | ok |
| b15_higher_order | <0.00005s | <0.00005s | 31× | 75 | 2 | ok |
| b16_nested_pipeline | 0.0001s | <0.00005s | 154× | 134 | 2 | ok |
| b17_explosion | 0.0001s | <0.00005s | 68× | 62 | 2 | ok |
| b18_stringless_foldmap | 0.0026s | 0.0022s | 1.17× | 202 | 6158 | ok |
| b19_pipeline_small | 0.0005s | <0.00005s | 808× | 206 | 2 | ok |
| b20_multisite | 0.0003s | <0.00005s | 37× | 162 | 74 | ok |

(The `<0.00005s` entries print as `0.0000s`; ratios are computed from unrounded times. Speedups >1000× occur where the residual is a constant.)

### Deforestation (intermediate `Pair` allocations, base vs optimized)

| benchmark | pairs_base | pairs_opt | ratio |
|---|---|---|---|
| b02_pipeline | 430 | 430 | 1.0000 |
| b16_nested_pipeline | 16 | 0 | 0.0000 |
| b19_pipeline_small | 80 | 0 | 0.0000 |
| b18_stringless_foldmap | 424 | 424 | 1.0000 |

Intermediates are fully eliminated on the pipelines that fold statically (b16, b19); b02/b18 retain their pair allocations (their folds stay dynamic) yet still agree — see Limitations.

### Code-explosion control (b17 family, expand-factor sweep K ∈ {1,2,4,8,16,32})

Residual size stayed **2 instructions at every K** (vs-base 0.03×); compile time <0.01 s per setting. The cost model never had to cut off growth on this family.

### Whistle necessity (`sum-acc 400`, driver unfold statistics)

| configuration | unfolds | folds | generalizations | residual funcs |
|---|---|---|---|---|
| with HE whistle | 4 | 2 | 2 | 1 |
| HE disabled (`embed → False`) | 60 | 0 | 0 | 0 |

Both residuals compute `80200`. Without the whistle the driver unfolds until budgets stop it; with it, generalization caps unfolding at a constant number of steps for this family.

### Not measured

- Fuzz campaigns beyond 2 000 programs (the harness supports arbitrarily many via `--n`; longer campaigns: unmeasured).
- Multi-worker fuzzing (`--workers > 1`), `--quick` timing deltas, and any platform other than this macOS/CPython 3.13.5 machine: unmeasured.
- Historical claims in git commit messages (e.g. earlier 2 000-seed campaigns, 18-benchmark agreement): unmeasured by this session; current-state equivalents are the numbers above.

## Fixed during documentation

One minimal fix was required; everything else documented worked as-is.

1. **`sc/compiler.py` — `compile_source(..., collect_stats=True)` broke on the phase-1 fast path.** When a program fully static-evaluates within its step budget (common), the early return returned bare `BytecodeProgram`, violating the `collect_stats=True → (program, stats)` contract used by `sc/fuzzer.check_one`. Every fuzz seed crashed with `TypeError: cannot unpack non-iterable BytecodeProgram object` (observed: 300/300 seeds failing). Fix: honor `collect_stats` on that path (`if collect_stats: return bp, stats`), which changes nothing for default callers. After the fix: 300/300 clean, then 2000/2000 clean; smoke/super suites re-run green.

Note: `git status` shows `PROMPT.md` modified in the working tree — that change pre-dates this documentation session and was left untouched, per instructions.

## Limitations & Known Issues

- **The idempotence report (`sc.bench`'s last section) fails on all 20 benchmarks.** Three distinct failure modes, all inside the decompile-recompile round trip (caught per-benchmark; the rest of `sc.bench` completes):
  1. `RecursionError` — `decompile.program_to_source` renders deeply-nested residual terms with plain Python recursion and blows the interpreter's stack on large residuals (most benchmarks).
  2. `KeyError('<int>')` on reparse — for residuals consisting of a single folded constant, `_atom` returns a bare Python string (`str(987)`), which `sexp.pretty` then prints quoted (`"987"`); reparsing yields an unbound variable, verified directly.
  3. `AssertionError("rhs 'rdirect'")` — the decompiler has no case for the `rdirect` bail-path call kind emitted by the driver's cost-model fallback.
  Fixing these requires more than minimal edits, so they are left as-is; the core pipeline does not depend on the decompiler.
- **Deforestation is data-dependent**: b02_pipeline and b18_stringless_foldmap show zero reduction in intermediate pair allocations (both still produce correct output). Only pipelines whose consumers fold away statically get full elimination.
- **Specialization can grow code**: `interpreter_specialization` produced a 4.39× larger program (still faster); `boxes_effects` grew 7%. The `expand_factor`/`budget` declares exist to trade these off.
- **Effect-heavy loops don't speed up** (b03, b08, b11 ≈ 1.0×): box operations are deliberately opaque (rule E1), so mutation-driven loops specialize only in their arithmetic.
- **Language subset**: no floating point; user-level strings exist only as literals for `print`-adjacent use; `set!` on variables is rejected (boxes only); `while` is rejected (use recursion); `letrec` bindings must be lambdas; `quote` supports ints, bools, symbols, and lists.
- **Deep non-tail recursion in the oracle** relies on a big-stack thread and a 20 M recursion limit (`bigstack.py`); extremely deep programs may still hit platform limits. The bytecode VM itself is iterative and unaffected.
- **Whistle heuristics are tuned, not proven**: embedding depth caps (400), value-tree depth caps (60), bounded cons-tail digging (24 entries), and the countdown-fuel mask trade completeness for termination; pathological shapes may whistle too eagerly (less specialization) or rely on budget bail-outs (more code). Termination of the driver itself is enforced structurally (budgets, history/function caps, `Bail` fallback), not by the whistle alone.
- **Single-threaded VM**: no concurrency primitives; `print` is the only I/O; integers are arbitrary-precision Python ints (no overflow semantics).
- Timings above are micro-benchmarks on sub-millisecond workloads for the fastest rows; treat ratios like ">1000×" as indicative of constant-folding, not steady-state throughput claims.
