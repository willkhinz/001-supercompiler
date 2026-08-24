(define (power b n) (if (= n 0) 1 (* b (power b (- n 1)))))
(+ (power 3 12) (power 2 16))
