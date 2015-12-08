(define
  (is-bound? x lcexp)
  (cond
    [ (list? lcexp) 
      (cond 
        [ (null? lcexp) #f ]
        [ (eq? (car lcexp) 'lambda)
          (cond
            [ (eq? x (caadr lcexp)) #t ]
            [ #t (is-bound? x (caddr lcexp)) ] ) ]
        [ #t (or (is-bound? x (car lcexp)) (is-bound? x (cadr lcexp)) ) ] ) ]
    [ #t #f ] ) )

;; A little unit test of the above:
;; (isbound? 'x '(gnarly ((lambda (y) (func1 x y)) (lambda (x) (car x)) ) ) )

;(define
;  (occurs-free? x lcexp)
;  (cond
;    [ (list? lcexp)
;      (cond 
;        [ (null? lcexp) #t ]
;        [ (eq? (car lcexp) 'lambda)
;          (cond
;            [ (eq? x (caadr lcexp)) #f ]
;            [ #t (occurs-free? x (caddr lcexp)) ] ) ]
;        [ #t (or (occurs-free? x (car lcexp)) (occurs-free? x (cadr lcexp))) ] ) ]
;    [ #t #t ] ) )

;; (occurs-free? 'x '(gnarly ((lambda (y) (func1 y)) (lambda (x) (car x)) ) ) )

;; Ah!  This is designed to parse/process Lambda calculus expressions,
;; and Lambda calculus does not allow for list-like structures, unless
;; you synthesize them.  So, the language doesn't actually permit 
;; LISP-style function calls like (func1 x y)!
;;
;; If we define the following:
;;   first ::= (lambda (x) (lambda (y) x))
;;   second ::= (lambda (x) (lambda (y) y))
;; then
;;     ((first a) b) ==> ( ((lambda (x) (lambda (y) x)) a) b )
;;                   ==> ( (lambda (y) a) b )
;;                   ==> a
;;   and also
;;     ((second a) b) ==> ( ((lambda (x) (lambda (y) y)) a) b )
;;                    ==> ( (lambda (y) y) b )
;;                    ==> b
;;
;; I *think* this was the way to construct "pairs" in lambda-calculus:
;; make-pair ::= (lambda (e2) ( (lambda (e1) ((lambda (pfsel) pfsel) e1) ) e2) )
;; ((make-pair b) a) ==> ( ( (lambda (e2) ( (lambda (e1) ((lambda (pfsel) pfsel) e1) ) e2) ) b ) a )
;;                   ==> ( (lambda (e1) (((lambda (pfsel) pfsel) e1) b) ) a )
;;                   ==> (((lambda (pfsel) pfsel) a) b) 
;;
(define 
  make-pair1
  (lambda (e2)
    [(lambda (e1)
      [ (lambda (pfsel) pfsel) e1 ] ) e2 ] ) )

(define 
  first
  (lambda (x) (lambda (y) x)))
(define 
  second
  (lambda (x) (lambda (y) y)))

(define 
  make-pair
  (lambda (pfsel)
    (lambda (e2) [(lambda (e1) (pfsel e1)) e2 ] ) ) )
(define 
  make-pair2
  (lambda (pfsel)
    (lambda (e2) [ (lambda (e1) (pfsel e1)) e2 ] ) ) )
(define 
  make-pair3
  (lambda (e1)
    [ lambda (e2)
       ( lambda (pfsel) ((pfsel e1) e2) ) ] ) )
(define
  (occurs-free? x lcexp)
  (cond
    [ (symbol? lcexp) (eqv? x lcexp) ]
    [ (eqv? (car lcexp) 'lambda)
      (and (not (eqv? (car (car (cdr lcexp))) x) )
           (occurs-free? x (car (cdr (cdr lcexp))) ) ) ]
    [ #t (or (occurs-free? x (car lcexp)) (occurs-free? x (car (cdr lcexp))) ) ] ) )
