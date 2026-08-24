(define (f n)
  (try (if (= n 0) (raise 'done) (begin (quot 100 n) (f (- n 1))))
       (lambda (e) 999)))
(f 1500)
