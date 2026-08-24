(define (gcd a b) (if (= b 0) a (gcd b (rem a b))))
(define (build n) (if (= n 0) '() (cons n (build (- n 1)))))
(define (foldgcd xs) (if (null? xs) 0 (gcd (car xs) (foldgcd (cdr xs)))))
(foldgcd (build 60))
