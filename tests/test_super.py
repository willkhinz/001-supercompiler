"""End-to-end supercompiler tests: specialized output must agree with the
reference interpreter AND the unoptimized VM, with real speedups on
classic cases."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sc.sexp import parse_all
from sc.lang import desugar_top
from sc.bigstack import run_program_bigstack
from sc.compiler import compile_source, CompileOptions, compile_unspecialized
from sc.vm import run as vm_run
from sc.decompile import program_to_source


def norm(v, depth=8):
    from sc.semantics import Pair, Box, Closure
    if depth <= 0:
        return "..."
    if isinstance(v, Pair):
        return ("p", norm(v.hd, depth - 1), norm(v.tl, depth - 1))
    if isinstance(v, Box):
        return ("box", norm(v.v, depth - 1))
    if isinstance(v, Closure) or hasattr(v, "fid"):
        return "#proc"
    if v is None:
        return "()"
    if isinstance(v, tuple) and len(v) == 2 and v[0] == "err":
        return v
    return v


def outcome(src, mode="ref"):
    if mode == "ref":
        prog = desugar_top(parse_all(src))
        r = run_program_bigstack(prog)
        return (r["out"], r["status"], norm(r["value"]))
    bp = compile_source(src) if mode == "opt" else compile_unspecialized(src)
    r = vm_run(bp)
    return (r["out"], r["status"], norm(r["value"]))


CASES = {
"fib": """
(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(fib 18)
""",
"pipeline": """
(define (range a b) (if (< a b) (cons a (range (+ a 1) b)) '()))
(define (map f xs) (if (null? xs) '() (cons (f (car xs)) (map f (cdr xs)))))
(define (filter p xs)
  (if (null? xs) '()
      (if (p (car xs)) (cons (car xs) (filter p (cdr xs)))
          (filter p (cdr xs)))))
(define (fold f z xs) (if (null? xs) z (fold f (f z (car xs)) (cdr xs))))
(define (inc x) (+ x 1))
(define (odd? x) (= (rem x 2) 1))
(print (fold + 0 (map inc (filter odd? (range 0 40)))))
(range 0 5)
""",
"power": """
(define (power b n) (if (= n 0) 1 (* b (power b (- n 1)))))
(power 3 10)
""",
"ackermann_small": """
(define (ack m n)
  (cond ((= m 0) (+ n 1))
        ((= n 0) (ack (- m 1) 1))
        (else (ack (- m 1) (ack m (- n 1))))))
(ack 2 3)
""",
"boxes_effects": """
(define b (box 0))
(define (bump! k)
  (begin
    (print k)
    (set-box! b (+ (unbox b) 1))
    (unbox b)))
(begin
  (bump! 1)
  (bump! 2)
  (print (+ (bump! 3) (begin (set-box! b 100) (unbox b))))
  (unbox b))
""",
"exceptions_flow": """
(define (safe f n)
  (try (f n) (lambda (e) (cons 'err e))))
(define (div2 n) (quot n 2))
(define (boom-if-zero n) (if (= n 0) (raise 'was-zero) (div2 n)))
(list (safe boom-if-zero 10) (safe boom-if-zero 0))
""",
"closures_pipeline": """
(define (make-adder n) (lambda (x) (+ x n)))
(define add1 (make-adder 1))
(define (twice f) (lambda (x) (f (f x))))
((twice add1) 41)
""",
"mutual_recursion": """
(define (ev? n) (if (= n 0) #t (od? (- n 1))))
(define (od? n) (if (= n 0) #f (ev? (- n 1))))
(ev? 50)
""",
"interpreter_specialization": """
; tiny expression interpreter specialized to a fixed program
(define (eval-expr e env)
  (if (pair? e)
      (let ((op (car e)) (args (cdr e)))
        (if (equal? op '+)
            (+ (eval-expr (car args) env) (eval-expr (car (cdr args)) env))
            (if (equal? op '*)
                (* (eval-expr (car args) env) (eval-expr (car (cdr args)) env))
                (raise 'bad-op))))
      (if (pair? (assq-ref e env))
          (unbox (assq-ref e env))
          e)))
(define (assq-ref k env) (if (null? env) #f (if (eq? (car (car env)) k) (car (cdr (car env))) (assq-ref k (cdr env)))))
(define env (list (list 'x (box 5)) (list 'y (box 7))))
(eval-expr '(+ (* x x) (* y y)) env)
""",
}


def main():
    fails = 0
    for name, src in CASES.items():
        ref = outcome(src, "ref")
        base = outcome(src, "base")
        opt = outcome(src, "opt")
        ok = (ref == base == opt)
        bp = compile_source(src)
        bu = compile_unspecialized(src)
        sz_o = bu.total_instructions()
        sz_s = bp.total_instructions()
        t_b = timeit(src, False)
        t_s = timeit(src, True)
        tag = "ok " if ok else "FAIL"
        print("%s %-26s size %4d->%4d (%.2fx) time %.3g->%.3g speedup %.2fx"
              % (tag, name, sz_o, sz_s, sz_s / max(1, sz_o), t_b, t_s,
                 t_b / max(t_s, 1e-9)))
        if not ok:
            fails += 1
            print("   ref:", ref)
            print("   base:", base)
            print("   opt:", opt)
    sys.exit(1 if fails else 0)


def timeit(src, spec):
    bp = compile_source(src) if spec else compile_unspecialized(src)
    best = 1e9
    for _ in range(3):
        t0 = time.perf_counter()
        r = vm_run(bp)
        dt = time.perf_counter() - t0
        best = min(best, dt)
        if r["status"] == "timeout":
            break
    return best


if __name__ == "__main__":
    main()
