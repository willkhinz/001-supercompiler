(define (sum-acc n acc) (if (= n 0) acc (sum-acc (- n 1) (+ acc n))))
(sum-acc 4000 0)
