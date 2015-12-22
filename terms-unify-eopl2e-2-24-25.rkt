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

(define var-term?
  (lambda (x)
    (cases term x
      (var-term (xi) #t)
      (else #f)) ) )

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
      (constant-term (datum) ss)
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

;; N.B. This is a "tagged-data-structure" implmentation
;; for the substitution abstract syntax tree.
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

;; At first, I didn't clearly understand the role of empty-subst
;; when using an AST representation.
;; The purpose of empty-subst is to evaluate to a data structure
;; or a value such that
;;   (equal? (apply-subst (empty-subst) sym) (var-term sym))
;; From the imperative/procedural perspective, empty-subst
;; "constructs" an empty substitution, suitable for further
;; "extension" via extend-subst.
(define empty-subst
  (lambda () (subst-list '()) ) )

(define apply-subst-r
  (lambda (sl sym)
    (cond ((null? sl) (var-term sym))
          ;; I guess it might be more "explicit" to say:
          ;; ((equal? (empty-subst) sl) (var-term sym)) ?
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
       (subst-list (extend-subst-r i t sl))) ) ) )

;(extend-subst
; 'w (parse-term '("ugh" u v))
; (parse-subst
;  `( (sym1 ,(parse-term '("eff" x y)) )
;     (w ,(parse-term '("gee" m n)))
;     (q ,(parse-term '(m n o))) ) ) )

;; (parse-term '("append" ("cons" w x) y ("cons" w z)))

;; subst-in-term:
;; Takes a term and a substitution and walks through the
;; term replacing each variable with its association in the
;; substitution, much like the procedure subst of section
;; 1.2.2.
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
       (app-term
        (subst-in-loterms loterms subst)) ) ) ) )

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
;;
;(equal?
; (apply-subst
;  (parse-subst
;   `( (sym1 ,(parse-term '("eff" x y)) )
;      (w ,(parse-term '("gee" m n)))
;      (q ,(parse-term '(m n o))) ) )
;  'z)
; (parse-term 'z) )
;
;(equal?
; (extend-subst
;  'w
;  (parse-term '("ugh" u v))
;  (parse-subst
;   `( (sym1 ,(parse-term '("eff" x y)) )
;      (w ,(parse-term '("gee" m n)))
;      (q ,(parse-term '(m n o))) ) ) )
; (parse-subst
;  `( (sym1 ,(parse-term '("eff" x y)) )
;     (w ,(parse-term '("ugh" u v)))
;     (q ,(parse-term '(m n o))) ) ) )
;; 

;; "Finally, implement subst-in-terms that takes a list
;; of terms."
;; N.B. I think what the exercise is asking for is 
;; based on something I have already written, and this
;; is also a consequence of the abstract syntax tree
;; representation of substitutions.
(define subst-in-terms
  (lambda (loterms subst)
    (cond
      ((null? loterms) loterms)
      (else
       (cons
        (subst-in-term (car loterms) subst)
        (subst-in-terms (cdr loterms) subst) ) ) ) ) )
     

;(equal?
; (subst-in-terms
;  (list
;   (parse-term '("append" ("cons" w x) y ("cons" w z)))
;   (parse-term '("append" x1 y z1))
;   )
;  (parse-subst
;   `( (sym1 ,(parse-term '("eff" x y)) )
;      (x1   ,(parse-term '("cons" w x)) )
;      (z1   ,(parse-term '("cons" w z)) )
;      (y    ,(parse-term "replacement-of-y!") ) ) ) )
; (list
;  (parse-term '("append" ("cons" w x) "replacement-of-y!" ("cons" w z)) )
;  (parse-term '("append" ("cons" w x) "replacement-of-y!" ("cons" w z)) ) ) )
;
;(subst-in-term
; (parse-term '("append" ("cons" w x) y ("cons" w z)))
; (parse-subst
;   `( (sym1 ,(parse-term '("eff" x y)) )
;      (x1   ,(parse-term '("cons" w x)) )
;      (z1   ,(parse-term '("cons" w z)) )
;      (y    ,(parse-term "replacement-of-y!") ) ) ) )
;
;(subst-in-term
; (parse-term '("append" x1 y z1))
; (parse-subst
;   `( (sym1 ,(parse-term '("eff" x y)) )
;      (x1   ,(parse-term '("cons" w x)) )
;      (z1   ,(parse-term '("cons" w z)) )
;      (y    ,(parse-term "replacement-of-y!") ) ) ) )


;; So, now we move on to Exercise 2.25:
;; An important use of substitutions is in the
;;   unification problem.
;; The unification problem is:
;;   Given two terms, t and u, can they be made equal?
;;   More precisely, is there a substitution s
;;   such that
;;     (subst-in-term t s)
;;   and
;;     (subst-in-term u s)
;;   are equal?
;; We say that such an s
;;   unifies
;; t and u.
;; There may be many such unifiers.  If so, there will
;; always be one that is the most general.
;;
;; The following shows part of an algorithm to find the most
;; general unifying substitution.  If no such unifier exists,
;; it returns #f:

;; Just "hack" to ensure that the all-ids-term function is
;; used by the unify-term function when it applies "all-ids."
(define all-ids all-ids-term)  

(define unify-term
  (lambda (t u)
    (cases term t
      (var-term (tid)
       ;; (unit-subst tid u) )
       (if (or (var-term? u) (not (memv tid (all-ids u))))
           (unit-subst tid u)
           #f))
      (else
       (cases term u
         (var-term (uid)
          (unify-term u t))
         (constant-term (udatum)
          (cases term t
            (constant-term (tdatum)
             (if (equal? tdatum udatum) (empty-subst) #f))
            (else #f)))
         (app-term (us)
          (cases term t
            (app-term (ts)
             (unify-terms ts us))
            (else #f))) ) ) ) ) )

(define unify-terms
  (lambda (ts us)
    (cond
      ((and (null? ts) (null? us)) (empty-subst))
      ((or (null? ts) (null? us)) #f)
      (else
       (let
           ((subst-car (unify-term (car ts) (car us))))
         (if (not subst-car)
             (#f)
             (let
                 ((new-ts (subst-in-terms (cdr ts) subst-car))
                  (new-us (subst-in-terms (cdr us) subst-car)) )
               (let
                   ((subst-cdr (unify-terms new-ts new-us) ) )
                 (if (not subst-cdr)
                     #f
                     (compose-substs subst-car subst-cdr)) )
               ) ) ) ) ) ) )

;; Complete the algorithm by extending the substitution interface
;; with two functions:
;;   unit-subst and compose-substs
;; The application
;;   (unit-subst i t)
;; returns a substitution that replaces symbol i with term t
;; and replaces any other symbol by its trivial association.
;;
;; The application
;;   (compose-substs s1 s2)
;; returns a substitition s' such that
;;   for all terms t,
;;      (equal?
;;         (subst-in-term t s')
;;         (subst-in-term (subst-in-term t s1) s2) )
;;
;; The memv test inside unify-term is called the "occurs check."
;; Create an example to illustrate that this is necessary.

(define unit-subst
  (lambda (i t)
    (subst-list (list (list i t))) ) )

;; The early inclination for the design of compose-substs
;; is to, somehow, iteratively/recursively apply
;;   extend-subst
;; against s1, from the items inside s2?

(define compose-substs
  (lambda (s1 s2)
    (letrec
        ((subst-of-subst
          (lambda (s1 s2)
            (cond ((null? s1)
                   (cases subst s2
                     (subst-list (sli) sli) ) )
                  (else
                   (let ((sym (caar s1))
                         (t   (cadar s1)) )
                     (cons (list sym (subst-in-term t s2))
                           (subst-of-subst (cdr s1) s2) ) )
                   ) ) ) ) )
      (cases subst s1
        (subst-list (sl1)
           (subst-list (subst-of-subst sl1 s2) ) ) ) ) ) )


(compose-substs
 (parse-subst `( (a ,(parse-term '("eff" z m f)) )
                 (ell ,(parse-term '(k z em))) ) )
 (parse-subst `( (z ,(parse-term '("cons" (a b) k) )) ) ) )

(define unparse-subst-r
  (lambda (sli)
      (cond ((null? sli) '())
            (else
             (let ((sym (caar sli))
                   (t   (cadar sli)))
               (cons (list sym (unparse-term t))
                     (unparse-subst-r (cdr sli)))))) ) )
(define unparse-subst
  (lambda (s)
    (cases subst s
      (subst-list (sli) (unparse-subst-r sli)))))

(let*
      ((t1 (parse-term '("eff" z m p)))
       (t2 (parse-term '(fm ("cons" f g) b k)) )
       (utr (unify-term t1 t2) ) )
    (list (unparse-term (subst-in-term t1 utr))
          (unparse-term (subst-in-term t2 utr))
          (list 'unparsed-subst (unparse-subst utr)) ) )


(let*
      ((t1 (parse-term '("eff" z (m x) p)))
       (t2 (parse-term '(fm ("cons" f g) (b (g n)) k)) )
       (utr (unify-term t1 t2) ) )
    (list (unparse-term (subst-in-term t1 utr))
          (unparse-term (subst-in-term t2 utr))
          (list 'unparsed-subst (unparse-subst utr)) ) )

(unify-term (parse-term '(q (p x y) (p y x)))
            (parse-term '(q z z)))
(unify-term (parse-term '(p x y))
            (parse-term '(p y x)))
(unify-term (parse-term '(p x y a))
            (parse-term '(p y x x)))

(unify-term (parse-term '("p" x y "a"))
            (parse-term '("p" y x x)))

(unify-term (parse-term '("q" ("p" x y) ("p" y x)))
            (parse-term '("q" z z)))

(unify-term (parse-term '("p" x y "a"))
            (parse-term '("p" y x x)))

(unify-term (parse-term '("p" x y) )
            (parse-term '("p" y x)))

