; exponential specialization potential: two independent counters
(define (f a b)
  (if (= a 0) b
      (if (= b 0) a
          (if (< a b) (f (- a 1) b) (f a (- b 1))))))
(f 14 12)
