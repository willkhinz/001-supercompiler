# Build: a whole-program supercompiler that provably never changes behavior

Write an optimizing whole-program partial evaluator / supercompiler for a real language (pick a Scheme, a Lua subset, or a strict ML — your choice, but it must be a language with closures, mutation, and exceptions). It performs aggressive interprocedural specialization: driving, generalization, folding, deforestation, and closure elimination. The point is not that it is fast; the point is that it is *aggressive and still correct*.

## Why this is brutal
- Supercompilation is a fixed-point process over an infinite tree of program states. Making it terminate requires a whistle (homeomorphic embedding or equivalent) and a generalization step, and getting those wrong yields either non-termination or no optimization at all.
- Correctness under mutation and effects destroys the pure-functional intuition. Specializing across a mutable cell or an exception boundary is where every naive implementation silently changes semantics.
- Code explosion is the default outcome. Aggressive specialization without a cost-model-driven cutoff produces a 400x binary.
- The bugs are semantic, invisible, and only appear on inputs nobody tested.

## Requirements
1. Full pipeline: parse, CPS or ANF normalize, drive, whistle-detect, generalize, fold, residualize, then a real backend (bytecode VM or C emission).
2. Deforestation: intermediate data structures in a `map`/`filter`/`fold` composition must be provably eliminated. Show it in the residual code.
3. Effects-correct: mutation, exceptions, and IO ordering must be preserved exactly. State the rules that make this sound.
4. Termination guarantee for the driving loop, with the whistle documented and its necessity demonstrated by a program that loops without it.
5. Cost model that bounds code growth to a configurable factor and chooses what to specialize. Report size/speed tradeoff curves.
6. A benchmark suite of at least 15 programs with measured speedups and code-size deltas versus unoptimized.
7. Optimization must be optional per-function and the compiler must be self-hosting-capable or explain precisely why not.

## Harness and tests
- **Differential fuzzer, the centerpiece:** generate random well-typed programs with effects, run optimized and unoptimized, compare full observable behavior — return value, output ordering, exception identity, and mutation traces. 500,000 programs minimum. Any divergence is a hard fail.
- **Whistle stress:** a program family whose driving tree grows without bound. Must terminate.
- **Effect ordering:** a program whose output order changes under naive specialization. Must be preserved.
- **Exception identity:** specialization must not turn a thrown exception into a different one, nor change whether one is thrown.
- **Code explosion:** a program family with exponential specialization potential. The cost model must cut it off; report where.
- **Deforestation proof:** assert zero allocation of intermediate lists in the residual for a composed pipeline.
- **Idempotence:** optimizing already-optimized output should be near-fixed-point. Report the delta.

## Deliverable
A complete, buildable implementation plus the verification harness as a runnable CLI. Use git and commit incrementally so progress is inspectable. Write a README stating: the architecture and why you chose it, the invariants you rely on, your measured results against ground truth or the reference implementation, and an explicit limits section — what this cannot do, and why. Any number in the README you did not actually measure must be labeled unmeasured. Never report a metric you did not compute.

Scope note: this is a multi-day-sized problem for a human team. Do not deliver a sketch, a skeleton, a subset, or a "production-ready foundation". Build the real thing, run the harness, fix what it finds, and iterate until the numbers are genuinely good.

DO NOT ASK ME ANY QUESTIONS. MAKE ASSUMPTIONS. DO NOT STOP UNTIL YOU ARE CONVICTED OF THE PERFECTION OF YOUR WORK
