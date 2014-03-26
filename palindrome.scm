(define palindrome?
  (lambda (l)
    (let*
        ((llen (length l))
         (dist (quotient llen 2)) )
      (letrec
          ((pal-in (lambda (l-half r-half l-size)
                     (cond ((equal? l-size dist)
                            (cond
                             ((odd? llen) (pal-out l-half (cdr r-half)) )
                             (else (pal-out l-half r-half))) )
                           (else
                            (pal-in (cons (car r-half) l-half) (cdr r-half) (+ 1 l-size))) ) ) )
           (pal-out (lambda (l-half r-half)
                      (cond ((and (null? l-half) (null? r-half)) #t)
                            ((equal? (car l-half) (car r-half)) (pal-out (cdr l-half) (cdr r-half)))
                            (else #f)) ) ) )
        (pal-in '() l 0) ) ) ) )

(define pal-in
  (lambda (l m r)
    (cond ((null? r) (cons (car m) l))
          (else (pal-in (cons (car m) l) (cdr m) (cddr r))))))

(define pal-in2
  (lambda (acc l r)
    (cond ((null? (cdr r)) (list acc l))
          (else (pal-in2 (cons (car l) acc) (cdr l) (cddr l) )))))

(define palindrome2?
  (lambda (l)
    (equal? (pal-in (cons (car l) '()) (cdr l) (cddr l)) (cdr l)) ) )

(define pal-in3
  (lambda (acc l r)
    ;; (display acc) (display l) (display r) (display "\n")
    (cond ((null? r)                       (equal? acc  l     ))
          ((and (pair? r) (null? (cdr r))) (equal? acc (cdr l)))
          (else (pal-in3 (cons (car l) acc) (cdr l) (cddr r))))))

(define palindrome3?
  (lambda (l)
    (pal-in3 (cons (car l) '()) (cdr l) (cddr l))))
;; Fine waste of time this has been; need a "cdr-multiplier" I reckon.
;; I have wasted enough time on this today.

;; Tests to see if the length of the list is even or odd
;; by checking to see if one or zero elements remains after
;; repeatedly removing two elements.
(define u-even?
  (lambda (lst)
    (cond ((null? lst) #t)  ;; this is a "base case"
          ((and (pair? lst) (null? (cdr lst))) #f)  ;; this is a "base case"
          (else (u-even? (cddr lst)) )  ;; this is the "inductive step"
          ) ) )

;; From a question posed in a set of lectures about a system called
;; Rascal.  Rascal is, afaict, a functional language for program
;; transformation (that was written in Java, or all things?)
(define fizz-buzz-out
  (lambda (x)
    (cond ((zero? (modulo x 15)) (list x 'FizzBuzz))
          ((zero? (modulo x  5)) (list x 'Buzz))
          ((zero? (modulo x  3)) (list x 'Fizz))
          (else          x))) )

(define list-gen
  (lambda (n)
    (letrec
        ((l-gen
          (lambda (n l)
            (cond ((zero? (- n 1)) (cons n l))
                  (else (l-gen (- n 1) (cons n l))) ) ) ))
      (l-gen n '()))) )

;; More efficient, linear-time cost, tail-recursive list-reversal
;; function.
(define i-reverse
  (lambda (l)
    (letrec
        ((tr-rev
          (lambda (rl l)
            (cond ((null? l) rl)
                  (else (tr-rev (cons (car l) rl) (cdr l)) ) ) ) ) )
      (tr-rev '() l) ) ) )

;;
;; Much more costly reverse function, because you end up paying for the
;; cost of traversing to the end of the first operand in order to append.
;; 
(define i-reverse2
  (lambda (l)
    (cond ((null? l) l)
          (else (append (i-reverse2 (cdr l)) (cons (car l) '()) ) ) ) ) )

