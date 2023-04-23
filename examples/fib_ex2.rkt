(define fib
  (lambda (n)
    (if (< n 2) ; 0 and 1 are the base cases
        n
        (+ (fib (- n 1)) (fib (- n 2))))))

