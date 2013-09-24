(define flatten-ugly
  (lambda (l)
    (cond
     ((null? l) '())
     ((list? (car l))
      (append (flatten-ugly (car l)) (flatten-ugly (cdr l))))
     (else
      (cons (car l) (flatten-ugly (cdr l))) ) ) ) )

(define flatten
  (lambda (l)
    (letrec
        ((flt-tr
          (lambda (se res)
            (cond
             ((null? se) res)
             ((list? (car se))
               (append (flt-tr (car se) '()) (flt-tr (cdr se) res)) )
             (else
              (flt-tr (cdr se) (cons (car se) res)) ) ) )) )
      (flt-tr l '()) ) ) )

(define f-compose
  (lambda (f g)
    (lambda (x) (f (g x))) ) )

(define end-cat
  (lambda (l i)
    (f-compose l (lambda (h) (cons i h)))) )

(define f-id
  (lambda (x) x) )

(define flatten2
  (lambda (l)
    (letrec
        ((flt-tr
          (lambda (se res)
            (cond
             ((null? se) res)
             ((list? (car se))
              (flt-tr (cdr se) (flt-tr (car se) res)))
             (else
              (flt-tr (cdr se) (end-cat res (car se))) ) ) ) ) )
      ((flt-tr l f-id) '()) ) ) )

(define flat-nice
  (lambda (se tl)
    (cond
     ((null? se) tl)
     ((list? se)
      (flat-nice (car se) (flat-nice (cdr se) tl)))
;;      (let*
;;          ((fst (car se))
;;           (rst (cdr se))
;;           (new-tl (flat-nice rst tl)) )
;;        (flat-nice fst new-tl) ) )
     (else
      (cons se tl) ) ) ) )

(define fltn2
  (lambda (l fsf)
    (cond
     ((null? l) fsf)
     ((list? (car l))
      ; When (list? (car l)), the result must be
      ; what we get when we flatten (car l),
      ; combined with the result of what we get
      ; when we flatten (cdr l), right?
      ; And this truly is a kind of function-composition,
      ; in disguise, isn't it?
      (fltn2 (car l) (fltn2 (cdr l) fsf)) )
      ; (fltn2 (cdr l) (fltn2 (car l) fsf)) )
     (else (cons (car l) (fltn2 (cdr l) fsf)) ) ) ) )
     ; (else (fltn2 (cdr l) (cons (car l) fsf)))) ) )