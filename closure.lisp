(define (test x)
  (begin
   (define yy 4)
   (* yy (+ x 4))))
(define yy 1)
(test (+ 4 yy))
