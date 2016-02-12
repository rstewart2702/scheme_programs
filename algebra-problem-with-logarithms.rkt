; The original problem:
;   "Solve for x in:
;    26 ^ (2*x + 5) = 6 ^ (3*x + 1)"
; The solution was derived as follows:
;    log(26^(2*x + 5))        = log(6^(3*x + 1))
; == (2*x+5)*log(26)          = (3*x+1)*log(6)
; == (2*x+5)*(log(26)/log(6)) = (3*x+1)
; == log(26)/log(6)           = (3*x+1)/(2*x+5)
; Now, let C = log(26)/log(6), so that the above equation becomes:
; == C                        = (3*x+1)/(2*x+5)
; == C*(2*x+5)                = (3*x+1)
; == 2*C*x + 5*C              =  3*x+1
; == 2*C*x - 3*x + 5*C        =  1
; == x*(2*C - 3)  + 5*C       =  1
; == x*(2*C - 3)              =  1 - 5*C
; == x                        =  (1 - 5*C)/(2*C -3)
; == 2*C*x - 3*x              =  1 - 5*C
; == x*(2*C - 3)              =  1 - 5*C
; == x                        =  (1 - 5*C)/(2*C - 3)

(define f-left
  (lambda (x)
    (* (log 6) (+ 1 (* 3 x))) ) )

(define f-right
  (lambda (x)
    (* (log 26) (+ 5 (* 2 x)))))

(define iter-apply
  (lambda (fn res n i)
    (if (equal? i 0)
        res
        (iter-apply fn (fn res n) n (- i 1)))))


(let*
    ((C   (/ (log 26)
             (log 6)) )
;     (eks (/ (- (* 5 C) 1)
;             (- 3 (* 2 C))) )
     (eks (/ (- 1 (* 5 C))
             (- (* 2 C) 3) ) )
     )
  (list (equal? (f-left eks) (f-right eks))
        (list (f-left eks) (f-right eks))
        (equal? (exp (* (+ 5 (* 2 eks)) (log 26)))
                (exp (* (+ (* 3 eks) 1) (log 6)) ) )
        (list (exp (* (+ 5 (* 2 eks)) (log 26)))
              (exp (* (+ (* 3 eks) 1) (log 6)) ) )
        (list (exp (f-left eks))
              (exp (f-right eks)))
;        (list (* 26 (exp (+ 5 (* 2 eks))) )
;              (* 6  (exp (+ 1 (* 3 eks)))))
        (iter-apply * (exp (+ 5 (* 2 eks))) (exp (+ 5 (* 2 eks))) 24)
        (iter-apply * 1                     (exp (+ 5 (* 2 eks))) 25) ) ) 

