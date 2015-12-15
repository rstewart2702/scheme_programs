;; Preparatory steps:
(load "eopl2e/code/interps/r5rs.scm")
(load "eopl2e/code/interps/define-datatype.scm")


(define list-of
  (lambda (pred)
    (lambda (l)
      (cond ((null? l) #t)
            (else (and (pred (car l))
                       ((list-of pred) (cdr l)) )) ) ) ) )

(define constant?
  (lambda (x) (or (number? x) (boolean? x) (string? x))))

;; Exercise 2.13:
;; "Define a term to be either a variable, a constant, (either a
;; string, a number, a boolean, or the empty list) or a list of terms.
;; We can use the folliwng data type to define the abstract syntax of terms:

(define-datatype term term?
  (var-term (id symbol?))
  (constant-term (datum constant?))
  (app-term (terms (list-of term?))) )

;; We represent a term using symbols for variables and lists
;; for app terms, while treating everything else as a constant.  Thus
;; the term
;;   ("append" ("cons" w x) y ("cons" w z))
;;
;; represents an abstract syntax tree that can be built by:
;;   (app-term
;;    (list
;;     (constant-term "append")
;;     (app-term
;;      (list
;;       (constant-term "cons") (var-term 'w) (var-term 'x)))
;;     (var-term 'y)
;;     (app-term
;;      (list
;;       (constant-term "cons") (var-term 'w) (var-term 'z)))))
;;
;; Implement parse-term, unparse-term, and all-ids for this term
;; language.

(define parse-list-of-terms
  (lambda (loterms)
    (cond
      ((null? loterms) '())
      (else (cons
             (parse-term (car loterms))
             (parse-list-of-terms (cdr loterms)) ) )
      ) ) )


(define parse-term
  (lambda (t)
    (cond
      ((symbol? t) (var-term t))
      ((constant? t) (constant-term t))
      ((list? t) (app-term (parse-list-of-terms t)) ) ) ) )

(define unparse-list-of-terms
  (lambda (loterms)
    (cond
      ((null? loterms) '())
      (else
       (cons
        (unparse-term (car loterms))
        (unparse-list-of-terms (cdr loterms))) ) ) ) )

(define unparse-term
  (lambda (t)
    (cases
        term t
      (var-term (id) id)
      (constant-term (datum) datum)
      (app-term
       (loterms)
       (list
        (unparse-term (car loterms))
        (unparse-list-of-terms (cdr loterms)) ) ) ) ) )

;; For the implementation of the all-ids-term, it seems that
;; a tail-recursive solution is quite a bit simpler (partly
;; because the code structure reflects the grammatical structure?)
;; and probably performs reasonably well:
(define all-ids-loterms
  (lambda (loterms ss)
    (cond
      ((null? loterms) ss)
      (else (all-ids-loterms
             (cdr loterms)
             (all-ids-term-r (car loterms) ss)))
      ) ) )

(define all-ids-term-r
  (lambda (t ss)
    (cases
        term t
      (var-term (id) (cons id ss))
      (constant-term (datum) (cons datum ss))
      (app-term
       (loterms)
       (all-ids-term-r
        (car loterms)
        (all-ids-loterms (cdr loterms) ss)) ) ) ) )
  
(define all-ids-term
  (lambda (t)
    (all-ids-term-r t '()) ) )

