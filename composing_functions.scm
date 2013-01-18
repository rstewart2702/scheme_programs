(define cons-er
  (lambda (x)
    (lambda (h) (cons x h)) ) )

(define c-wrap
  (lambda (fn h) (fn (cons 
    
;> (define cons-a (cons-er 'a))
;> cons-a
;#<procedure>
;> (cons-a 'b)
;(a . b)
;> (lambda (h) (cons 'a (cons 'b h)))
;#<procedure>
;> ((lambda (h) (cons 'a (cons 'b h))) ())
;(a b)
;> ((lambda (h) (cons-a (cons 'b h))) ())
;(a b)
;> 