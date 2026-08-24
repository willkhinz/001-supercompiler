"""Smoke tests: parse -> desugar -> refinterp, and ANF -> bytecode -> VM
agreement on a battery of small programs."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sc.sexp import parse_all, pretty
from sc.lang import desugar_top, size_of
from sc.front import closure_convert
from sc.anf import anf_convert
from sc import refinterp
from sc.bigstack import run_program_bigstack
from sc.bc import compile_ir
from sc.vm import run as vm_run

PROGS = {
"arith": "(print (+ 1 (* 2 3))) (- 10 (quot 7 2))",
"if": "(define (sign n) (if (< n 0) -1 (if (> n 0) 1 0))) (list (sign -5) (sign 0) (sign 9))",
"recursion": """
(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(print (fib 12)) (fib 15)
""",
"lists": """
(define (map f xs) (if (null? xs) '() (cons (f (car xs)) (map f (cdr xs)))))
(define (sum xs) (if (null? xs) 0 (+ (car xs) (sum (cdr xs)))))
(print (sum (map (lambda (x) (* x x)) (list 1 2 3 4 5))))
""",
"boxes": """
(define b (box 0))
(print (unbox b))
(set-box! b 42)
(begin (set-box! b (+ (unbox b) 1)) (print (unbox b)))
""",
"effects_order": """
(begin (print (+ (begin (print 1) 10) (begin (print 2) 20))) 'done)
""",
"exceptions": """
(define (safe-div a b) (try (quot a b) (lambda (e) -999)))
(print (safe-div 10 2))
(print (safe-div 10 0))
(print (try (begin (print 'before) (raise (list 1 2)) 99) (lambda (e) (cons 'caught e))))
""",
"exceptions_static": """
(print (try (+ 1 (raise 7)) (lambda (e) (* 100 e))))
""",
"closures": """
(define (adder n) (lambda (x) (+ x n)))
(define add5 (adder 5))
(define add7 (adder 7))
(print (add5 10))
(print ((adder 3) (add7 1)))
""",
"mutual": """
(define (even? n) (if (= n 0) #t (odd? (- n 1))))
(define (odd? n) (if (= n 0) #f (even? (- n 1))))
(print (even? 100)) (print (odd? 77))
""",
"named_let": """
(print (let loop ((i 0) (acc '()))
  (if (= i 5) acc (loop (+ i 1) (cons i acc)))))
""",
"tailrec": """
(define (count n acc) (if (= n 0) acc (count (- n 1) (+ acc 1))))
(print (count 50000 0))
""",
"errors": """
(print (try (car '()) (lambda (e) 'caught-car)))
(print (try (+ 1 #t) (lambda (e) 'caught-arith)))
(print (try (quot 5 0) (lambda (e) 'caught-div)))
""",
"shadow": """
(define x 1)
(define (f x) (+ x 1))
(print (let ((x 100)) (f x)))
""",
"higher_order_capture": """
(define (compose f g) (lambda (x) (f (g x))))
(define inc (lambda (x) (+ x 1)))
(define dbl (lambda (x) (* x 2)))
(define h (compose inc dbl))
(print (h 10))
(print ((compose dbl inc) 10))
""",
"deep_try": """
(print (try (try (raise 'inner) (lambda (e) (raise (list 're e)))) 
            (lambda (e) (cons 'outer e))))
""",
}


def ref_out(src):
    prog = desugar_top(parse_all(src))
    return run_program_bigstack(prog)


def bc_out(src):
    prog = desugar_top(parse_all(src))
    lifted = closure_convert(prog)
    ir = anf_convert(lifted)
    bp = compile_ir(ir)
    return vm_run(bp)


def norm(v, depth=8):
    from sc.semantics import Pair, Box, Closure
    if depth <= 0:
        return "..."
    if isinstance(v, Pair):
        return ("p", norm(v.hd, depth - 1), norm(v.tl, depth - 1))
    if isinstance(v, Box):
        return ("box", norm(v.v, depth - 1))
    if isinstance(v, Closure):
        return "#proc"
    if v is None:
        return "()"
    if isinstance(v, bool):
        return v
    if isinstance(v, int):
        return v
    if isinstance(v, str):
        return v
    if isinstance(v, tuple) and len(v) == 2 and v[0] == "err":
        return v
    return str(v)


def main():
    fails = 0
    for name, src in PROGS.items():
        r = ref_out(src)
        v = bc_out(src)
        okr = (r["out"] == v["out"] and r["status"] == v["status"]
               and norm(r["value"]) == norm(v["value"]))
        if not okr:
            fails += 1
            print("MISMATCH", name)
            print("  ref:", r["out"], r["status"], pretty_val(norm(r["value"])))
            print("  vm :", v["out"], v["status"], pretty_val(norm(v["value"])))
        else:
            print("ok", name, "->", v["out"], v["status"], pretty_val(norm(v["value"])))
    if fails:
        sys.exit(1)


def pretty_val(x):
    return str(x)


if __name__ == "__main__":
    main()
