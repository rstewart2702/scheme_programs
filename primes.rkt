(define find-isqrt
  (lambda (n)
    (letrec
        ((inner-isqrt
          (lambda (rc n)
            (let ((new-square (* rc rc)) )
              (cond
                ((< new-square n)
                 (inner-isqrt (+ 1 rc) n))
                ((equal? new-square n)
                 rc)
                ((< n new-square) (- rc 1)) ) ) ) ) )
      (inner-isqrt 2 n) ) ) )
;; So that gives us a "floor of the square root of n,"
;; by executing a linear search for the largest integer
;; whose square is less than or equal to n.

;; This would seem to be the starting point of a prime factorization
;; technique, yes?  For the answer calculated by
;;   (find-isqrt k)
;; should give us an upper limit on the search for prime factors of
;; k, correct?

;; So what does a "prime factorization search" look like?
;; Repeated subtraction to see if the remaining quantity equals zero?
;; Then, start searching 0 to (sqrt x) or 0 to (find-isqrt x) for
;; things which divide into x?

;; A sieve would definitely need to quickly search for composite's
;; already determined, plus primes already determined?
