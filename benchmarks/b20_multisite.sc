; many call sites with distinct literals: naive per-site specialization
; would duplicate the body per site; cost model must cut this off.
(define (w n acc) (if (= n 0) acc (w (- n 1) (+ acc 2))))
(list (w 1 0) (w 2 1) (w 3 2) (w 4 3) (w 5 4) (w 6 5)
      (w 7 6) (w 8 7) (w 9 8) (w 10 9) (w 11 10) (w 12 11))
