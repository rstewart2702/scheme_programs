;;#lang eopl
;; Needed to get the foldl function:
(require racket/list)

; This was derived from the definitions of free and bound
; variables given in the Michaelson book.
(define is-atom?
  (lambda (x)
    (or (symbol? x) (number? x) (string? x) (char? x)
        )))

(define is-list?
  (lambda (x)
    (or (null? x)
        (and (pair? x) (is-list? (cdr x)) ) ) ) )

; The "almost-simple" lambda-calculus expression grammar,
; in which there may be a list of symbols as the argument-list
; for a lambda:
;<Lcexpr> ::=
;  <Name>
;| (<Lcexpr> <Lcexpr>)
;| (lambda (<Lsym>) <Lcexpr>)

; We also want the "application-expressions" to allow for there to be
; multiple arguments for the function-invocation, i.e.,
;  <List-of-Lcexpr> ::=
;    ()
;  | (<Lcexpr> . <List-of-Lcexpr>)
;
; and I think that "(<Lcexpr> . <List-of-Lcexpr>)" can be shortened to:
;  ( {<Lcexpr>}+ )
; maybe?
;
; So the "slightly-more-complex" lambda calculus grammar
; should be:
;   <Lcexpr> ::=
;     <Name>
;   | <List-of-Lcexpr>
;   | (lambda (<Lsym>) <Lcexpr>)
;
;   <List-of-Lcexpr> ::=
;     ()
;   | (<Lcexpr> . <List-of-Lcexpr>)
;
;   <Lsym> ::=
;     ()
;   | (<Name> . <Lsym>)
;
; The BIG LESSON here is to go back to the grammar, whenever
; you need to do something non-trivial with the language you're
; trying to deal with.  Elaborations on language structures require
; some effort to codify in the grammar, and then the programs to
; traverse these structures become simpler to write.
;

(define lsym?
  (lambda (x)
    (or
      (null? x)
      (and (pair? x) (symbol? (car x)) (lsym? (cdr x))) ) ) )

(define in-lsym?
  (lambda (lsym x)
    (cond
      ((null? lsym) #f)
      (else (or (equal? x (car lsym)) (in-lsym? (cdr lsym) x)) )
      )
    ) )

(define is-lambda?
  (lambda (lce)
    (and (pair? lce) (eqv? 'lambda (car lce)) )
    ) )

(define free-in-lambda?
  (lambda (lce x)
    (let
        ((arg-list (cadr lce))
         (l-body   (caddr lce)) )
      (and (not (in-lsym? arg-list x)) (free? l-body x) ) ) ) )

(define free-in-appl?
  (lambda (lce x)
    (let ((func (car lce))
          (args (cdr lce))
          )
    (or (free? func x) (free? args x) )
    )
  )
  )

(define free? 
  (lambda (lce x)
    (cond
      ((is-lambda? lce) (free-in-lambda? lce x))
      ((pair? lce) (free-in-appl? lce x))
      ((is-atom? lce) (eqv? lce x))
      (else #f) ) ) )

;; EoPL states that a variable is bound in a lambda abstraction
;; according to the following rule:
;;   (or (and (in-lsym? arg-list x) (free? l-body x))
;;       (bound? l-body))
;; where x is the variable in question, and arg-list and l-body
;; are the arguments to the lambda-expr, and the body of the
;; lambda-expr.
;;
;; 
(define bound-in-lambda?
  (lambda (lce x)
    (let
        ((arg-list (cadr lce))
         (l-body   (caddr lce))
         )
      ;; The Michaelson book's rule:
      (or (in-lsym? arg-list x) (bound? l-body x) )
      ;; The EoPl2e rule:
      ;; (or (and (in-lsym? arg-list x) (free? l-body x))
      ;;     (bound? l-body x))
      )
    )
  )

(define bound-in-appl?
  (lambda (lce x)
    (let ((func (car lce))
          (args (cdr lce))
          )
      (or (bound? func x) (bound? args x) )
      )
    )
  )

(define bound?
  (lambda (lce x)
    (cond
      ((is-lambda? lce) (bound-in-lambda? lce x))
      ((pair? lce) (bound-in-appl? lce x))
      (else #f)
      )
    )
  )


(define bound-vars-lambda
  (lambda (lce)
    (let
        ((arg-list (cadr lce))
         (l-body   (caddr lce))
         )
      (cons (list arg-list lce) (all-bound-vars l-body) )
      )
    )
  )

(define bound-vars-appl
  (lambda (lce)
    (let*
        ((func (car lce))
         (args (cdr lce))
         (func-bv-list (all-bound-vars func))
         (args-bv-list (all-bound-vars args))
         )
      (cond
        ((and (null? func-bv-list) (null? args-bv-list)) '())
        ((null? func-bv-list) args-bv-list)
        ((null? args-bv-list) func-bv-list)
        (else (append func-bv-list args-bv-list))
        )
      )
    )
  )


(define all-bound-vars
  (lambda (lce)
    (cond
      ((is-lambda? lce) (bound-vars-lambda lce))
      ((pair? lce) (bound-vars-appl lce))
      (else '())
      )
    )
  )


(define free-vars-lambda
  (lambda (lce)
    (let*
        ((arg-list (cadr lce))
         (body-expr (caddr lce))
         (body-free-vars (all-free-vars body-expr))
         )
      (foldl
       (lambda (i a)
         (cond
           ; If the variable shows up in the arg-list,
           ; then don't include it in the "accumulated list of free variables."
           ((in-lsym? arg-list i) a)
           ; The variable didn't show up in the arg-list,
           ; so add it to the "accumulated list of free variables."
           (else (cons i a))
           )
         )
       '() ; Initially, the list of accumulated results starts out empty.
       body-free-vars ; This is the list of items over which we must "fold."
       )
      )
    )
  )

(define free-vars-appl
  (lambda (lce)
    (let*
        ((func (car lce))
         (args (cdr lce))
         (func-fv-list (all-free-vars func))
         (args-fv-list (all-free-vars args))
         )
      (cond
        ((and (null? func-fv-list) (null? args-fv-list)) '())
        ((null? func-fv-list) args-fv-list)
        ((null? args-fv-list) func-fv-list)
        (else (append args-fv-list func-fv-list) )
        )
      )
    )
  )

(define all-free-vars
  (lambda (lce)
    (cond
      ((is-lambda? lce) (free-vars-lambda lce))
      ((pair? lce) (free-vars-appl lce))
      ((symbol? lce) (list lce))
      (else '())
      )
    )
  )
