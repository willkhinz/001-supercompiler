(define (count n acc) (if (= n 0) acc (count (- n 1) (+ acc 1))))
(count 6000 0)
