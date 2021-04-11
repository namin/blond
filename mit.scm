(define add1 (lambda (n) (+ n 1)))
(define sub1 (lambda (n) (- n 1)))
(define atom? (lambda (x) (not (pair? x))))
(define (flush-output-port) (flush-output))
