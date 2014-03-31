(lambda-calculus-subst
 (parse-lambda-expr '(fun1 (lambda (x) (f x)) x y) )
 (parse-lambda-expr '(lambda (x) (g x)))
 'x)

;; should yield:
;;   (fun1 (lambda (x) (f x)) (lambda (x) (g x)) y)
;; but it doesn't, currently.

(lambda-calculus-subst
 (parse-lambda-expr '(lambda (p) (+ p x)))
 (parse-lambda-expr '(* p 3))
 'x)
;; correctly yields:
;;   (lambda (p0) (+ p0 (* p 3)))
;; because 