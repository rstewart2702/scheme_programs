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


;; Environment sample implementation, from Section 2.3:
(define empty-env
  (lambda ()
    '() ))

(define extend-env
  (lambda (syms vals env)
    (cons (list syms vals) env)))

(define apply-env
  (lambda (env sym)
    (if (null? env)
        (eopl:error 'apply-env "No binding for ~s" sym)
        (let
            ((syms (car (car env)))
             (vals (cadr (car env)))
             (env (cdr env)))
          (let ((pos (rib-find-position sym syms)))
            (if (number? pos)
                (list-ref vals pos)
                (apply-env env sym)))))))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                  (+ list-index-r 1)
                  #f))))))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))


(define rib-find-position list-find-position)

;; Exercise 2.24
;; Define a substitution to be a function from the set of Scheme
;; symbols to the set of terms (exercise 2.13, above).  The
;; interface for substitutions consists of
;;   (empty-subst)
;; which maps each variable to the corresponding var-term
;; (sometimes referred to as its trivial association);
;;   (extend-subst i t s)
;; which returns a new substitution like s, except that symbol
;; i is mapped to term t; and
;;   (apply-subst s i)
;; which returns the value of symbol i in substitution s.
;; Implement the data type of substitutions with both a
;; procedural representation and an abstract syntax tree
;; representation.
;;
;; Then implement a procedure
;;   subst-in-term 
;; that takes a term and a substitution and walks through the
;; term replacing each variable with its association in the
;; substitution, much like the procedure subst of section
;; 1.2.2.  Finally, implement subst-in-terms that takes a list
;; of terms.

(define subst-item?
  (lambda (si)
    (and
     (pair? si)
     (symbol? (car si))
     (term? (cadr si))) ) )

(define-datatype subst subst?
  (subst-list
   (sl (list-of subst-item?)) ) )

(define parse-subst-r
  (lambda (s)
    (cond
      ((null? s) '())
      ((pair? s)
       (cond
        ((subst-item? (car s))
         (cons
          (car s)
          (parse-subst-r (cdr s)) ) )
        (else
         (eopl:error
          'parse-subst-r
          "Invalid concrete syntax of list item ~s"
          (car s))) ) )
      (else
       (eopl:error
        'parse-subst-r
        "Invalid concrete syntax ~s"
        s) ) ) ) )

(define parse-subst
  (lambda (s)
    (cond ((null? s) (subst-list s))
          (else (subst-list (parse-subst-r s)) ) ) ) )

;;(parse-subst `( (sym1 ,(parse-term '("eff" x y)) ) (w ,(parse-term '("gee" m n))) ) )

(define empty-subst
  (lambda (sym) (var-term sym)) )

(define apply-subst-r
  (lambda (sl sym)
    (cond ((null? sl) (empty-subst sym))
          (else
           (let ((lsym (caar sl))
                 (trm (cadar sl))
                 (sl (cdr sl)) )
             (cond ((eqv? lsym sym) trm)
                   (else (apply-subst-r sl sym)) ) )
           ) ) ) )
(define apply-subst
  (lambda (s sym)
    (cases
        subst s
      (subst-list
       (sl)
       (apply-subst-r sl sym)) ) ) )

(define extend-subst-r
  (lambda (sym t sl)
    (cond ((null? sl) (cons (list sym t) sl) )
          (else
           (let ((s (caar sl))
                 (trm (cadar sl))
                 (sl (cdr sl)) )
             (cond ((eqv? s sym) (cons (list sym t) sl) )
                   (else (cons (list s trm)
                               (extend-subst-r sym t sl)) ) )
             ) ) ) ) )
(define extend-subst
  (lambda (i t s)
    (cases
        subst s
      (subst-list
       (sl)
       (extend-subst-r i t sl)) ) ) )

;; (extend-subst 'w (parse-term '("ugh" u v)) (parse-subst `( (sym1 ,(parse-term '("eff" x y)) ) (w ,(parse-term '("gee" m n))) (q ,(parse-term '(m n o))) ) ) )
;; (parse-term '("append" ("cons" w x) y ("cons" w z)))

(define subst-in-term
  (lambda (trm subst)
    (cases
        term trm
      (var-term
       (id)
       (apply-subst subst id) )
      (constant-term (datum) trm)
      (app-term
       (loterms)
       (list
        (subst-in-term (car loterms) subst)
        (subst-in-loterms (cdr loterms) subst) ))
    ) ) )

(define subst-in-loterms
  (lambda (loterms subst)
    (cond
      ((null? loterms) '())
      (else
       (cons
        (subst-in-term (car loterms) subst)
        (subst-in-loterms (cdr loterms) subst)) ) )
      ) )

;; '( (w ("eff" x y)) )