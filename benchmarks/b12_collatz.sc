(define (steps n) (if (<= n 1) 0 (+ 1 (steps (if (= (rem n 2) 0) (quot n 2) (+ (* 3 n) 1))))))
(steps 27)
