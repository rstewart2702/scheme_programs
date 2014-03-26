;; Preparatory steps:
(primitive-load "eopl2e/code/interps/r5rs.scm")
(primitive-load "eopl2e/code/interps/define-datatype.scm")

;; Grammar for define-datatype:
;; (define-datatype <type-name> <type-predicate-name>
;;   { (<variant-name> { ( <field-name> <predicate> ) }* ) }+ )

;; Grammar for cases:
;; (cases <type-name> <expression>
;;    { ( <variant-name> ({<field-name>}*) <consequent> ) }*
;;    (else <default>) )

;; BNF grammar for a kind of lambda calculus:
;; N.B. THIS IS A LAMBDA-CALCULUS GRAMMAR WHICH IS CLOSER
;; IN SPIRIT TO REGULAR SCHEME OR LISP.  THERE ARE TWO
;; ENHANCEMENTS:  LAMBDA-ABSTRACTIONS MAY USE AN ARBITRARY
;; NUMBER OF PARAMETERS, AND FUNCTION-APPLICATION EXPRESSIONS
;; MAY USE ZERO OR MORE ARGUMENTS AS WELL.  THIS IS WHY
;; THE CONCRETE SYNTAX BELOW SHOWS THAT THERE'S AT LEAST ONE
;; <lambda-expr> NON-TERMINAL.
;;   <lambda-expr> ::=  <identifier>
;;                   | (lambda ({<identifier>}*) <lambda-expr>)
;;                   | (if <lambda-expr> <lambda-expr> <lambda-expr>)
;;                   | ({<lambda-expr>}+)

;; The following is a nuanced transformation of the above in order
;; to help make the Kleene plus and Kleene star parts a bit more
;; explicit.
;;   <expr-list> ::= () | (<lambda-expr> . <expr-list>)
;;   <id-list> ::= () | (<identifier> . <id-list>)
;;   <lambda-expr> ::=  <identifier>
;;                   | (lambda <id-list> <lambda-expr>)
;;                   | (if <lambda-expr> <lambda-expr> <lambda-expr>)
;;                   | (<lambda-expr> . <expr-list>)


;; Remember, the define-datatype is intended to capture,
;; specify, the "abstract syntax," the form and composition
;; of the abstract syntax tree structure.  (This is also
;; called the "internal representation.")  The BNF grammar,
;; remember, specifies the "concrete" syntax, or "external
;; representation."
;;
;; Later, there will be "parse" function that maps from
;; the concrete syntax representation to the abstract syntax
;; representation, and there will be an "unparse" function
;; which maps from the abstract syntax back to a concrete
;; representation.

;; First, the abstract syntax for the lambda-calculus grammar
;; above:
(define-datatype identifier identifier?
  (id-i
   (i symbol?)) )

(define-datatype id-list id-list?
  (empty-id-list)
  (non-empty-id-list
   (first-id identifier?)
   (rest-ids id-list?)))

;; (define-datatype expr-list expr-list?
;;   (an-expr-list (expr-list-data (genl-list-of lambda-expr?)) ) )
(define-datatype expr-list expr-list?
  (empty-expr-list)
  (non-empty-expr-list
   (first-expr lambda-expr?)
   (rest-exprs expr-list?) ) )

(define const?
  (lambda (x) (or (number? x) (boolean? x) (string? x))) )

(define-datatype lambda-expr lambda-expr?
  (const-expr
   (eks const?) )
  (id-expr
   (id identifier?))
  ;; The following two variants are useful for representing
  ;; "lexically addressed" identifiers:
  (id-bound-expr
   (id identifier?)
   (lex-id-dist number?)
   (lex-id-posn number?))
  (id-free-expr
   (id identifier?))
  ;;
  (lambda-abst ;; "lambda abstraction?"
   (ids id-list?) (body lambda-expr?))
  (if-expr
   (test-expr lambda-expr?)
   (true-expr lambda-expr?)
   (false-expr lambda-expr?))
  (appl-expr
   (rator lambda-expr?)
   (rands expr-list?) ) )

;; We MUST be able to calculate an abstract-syntax-tree version of
;; lambda-expr's, and that is the purpose of this function:
(define parse-le-id-list
  (lambda (x)
    (cond ((null? x) (empty-id-list))
          (else
           (non-empty-id-list (id-i (car x))
                              (parse-le-id-list (cdr x)))))))

(define parse-le-expr-list
  (lambda (x)
    (cond ((null? x) (empty-expr-list))
          (else
           (non-empty-expr-list (parse-lambda-expr (car x))
                                (parse-le-expr-list (cdr x)))))))

(define parse-lambda-expr
  (lambda (datum)
    (cond
     ((const? datum) (const-expr datum))
     ((symbol? datum) (id-expr (id-i datum)))
     ((pair? datum)
      (cond
       ((and (symbol? (car datum))
             (eqv? 'lambda (car datum)))
        (lambda-abst
         (parse-le-id-list (cadr datum))
         (parse-lambda-expr (caddr datum))) )
       ((and (symbol? (car datum))
             (eqv? 'if (car datum)))
        (if-expr
         (parse-lambda-expr (cadr datum))
         (parse-lambda-expr (caddr datum))
         (parse-lambda-expr (cadddr datum))) )
       (else
        (appl-expr
         (parse-lambda-expr (car datum))
         (parse-le-expr-list (cdr datum)) ) ) ) )
     (else (eopl:error 'parse-lambda-expr
                       "Invalid concrete syntax ~s" datum)))))

(define unparse-ids
  (lambda (ids)
    (cases
     id-list ids
     (empty-id-list () '())
     (non-empty-id-list
      (first-id rest-ids)
      (cases
       identifier first-id
       (id-i
        (i)
        (cons i (unparse-ids rest-ids))) ) ) ) ) )

(define unparse-expr-list
  (lambda (rands)
    (cases
     expr-list rands
     (empty-expr-list () '())
     (non-empty-expr-list
      (first-expr rest-exprs)
      (cons (unparse-lambda-expr first-expr)
            (unparse-expr-list rest-exprs))) ) ) )

(define unparse-lambda-expr
  (lambda (ast)
    (cases
     lambda-expr ast
     (id-expr
      (id)
      (cases
       identifier id
       (id-i
        (i)
        i)))
     (const-expr (eks) eks)
     ;;
     ;; Two cases to handle the cases of identifiers
     ;; "decorated" with lexical depth information
     (id-bound-expr
      (id d p)
      (list
       (cases
        identifier id
        (id-i (i) i))
       ': d p))
     (id-free-expr
      (id)
      (list
       'free
       (cases
        identifier id
        (id-i (i) i))) )
     ;;
     (lambda-abst
      (ids body)
      (list
       'lambda
       (unparse-ids ids)
       (unparse-lambda-expr body)))
     (if-expr
      (test-expr true-expr false-expr)
      (list
       'if
       (unparse-lambda-expr test-expr)
       (unparse-lambda-expr true-expr)
       (unparse-lambda-expr false-expr)))
     (appl-expr
      (rator rands)
      (cons
       (unparse-lambda-expr rator)
       (unparse-expr-list rands) ) ) ) ) )

;; The foregoing, hopefully, will provide what we need in order to
;; derive versions of the occurs-free? and occurs-bound?
;; functions which will be more readable because they use the 
;; nicer lambda-expr datatype, and the associated pieces.
;; In conjuction with the new datatype, defined by define-datatype,
;; we use the cases construct:

;; First a couple of helper-functions:
;; (define occurs-in
;;   (lambda (x ids)
;;     (cond ((null? ids) #f)
;;           ((eqv? x (car ids)) #t)
;;           (else (occurs-in x (cdr ids)) ) ) ) )

(define occurs-in
  (lambda (x ids)
    (cases
     id-list ids
     (empty-id-list () #f)
     (non-empty-id-list
      (first-id rest-ids)
      (cases
       identifier first-id
       (id-i
        (i)
        (or (eqv? x i)
            (occurs-in x rest-ids)))))) ) )

;; (define occurs-free-helper
;;   (lambda (x rands)
;;     (cond ((null? rands) #f)
;;           ((occurs-free? x (car rands))

(define occurs-free-helper
  (lambda (x rands)
    (cases expr-list rands
           (empty-expr-list () #f)
           (non-empty-expr-list
            (first-expr rest-exprs)
            (or (occurs-free? x first-expr)
                (occurs-free-helper x rest-exprs)) ) ) ) )

(define occurs-free?
  (lambda (x E)
    (cases lambda-expr E
           (id-expr
            (id)
            (cases
             identifier id
             (id-i (i) (eqv? x i))) )
           (const-expr
            (eks)
            #f)
           ;;
           (id-bound-expr
            (id d p)
            (cases
             identifier id
             (id-i (i) (eqv? x i)) ) )
           (id-free-expr
            (id)
            (cases
             identifier id
             (id-i (i) (eqv? x i)) ) )
           ;;
           (lambda-abst
            (ids body)
            (and (not (occurs-in x ids))
                 (occurs-free? x body) ) )
           (if-expr
            (test-expr true-expr false-expr)
            (or (occurs-free? x test-expr)
                (occurs-free? x true-expr)
                (occurs-free? x false-expr) ) )
           (appl-expr
            (rator rands)
            (or (occurs-free? x rator)
                (occurs-free-helper x rands)) ) ) ) )

(define occurs-bound?
  (lambda (x E)
    (cases lambda-expr E
           (id-expr
            (identifier)
            #f)
           (const-expr
            (eks)
            #f)
           ;;
           (id-bound-expr
            (id d p)
            #f)
           (id-free-expr
            (id)
            #f)
           ;;
           (lambda-abst
            (ids body)
            (or (and (occurs-in x ids)
                     (occurs-free? x body))
                (occurs-bound? x body)))
           (if-expr
            (test-expr true-expr false-expr)
            (or (occurs-bound? x test-expr)
                (occurs-bound? x true-expr)
                (occurs-bound? x false-expr)))
           (appl-expr
            (rator rands)
            (or (occurs-bound? x rator)
                (occurs-bound-helper x rands))))))

(define occurs-bound-helper
  (lambda (x rands)
    (cases expr-list rands
           (empty-expr-list () #f)
           (non-empty-expr-list
            (first-expr rest-exprs)
            (or (occurs-bound? x first-expr)
                (occurs-bound-helper x rest-exprs))))))

;; BNF grammar for the following exercises
;; (this is closer to the full Scheme grammar)
;; each production rhs has the "abstract syntax" representation
;; underneath it on the next line, enclosed in |[]|
;; <expression> ::=   <number>
;;                    |[lit-exp (datum)]|
;;                  | <var-exp>
;;                    |[var-exp (id)]|
;;                  | (if <expression> <expression> <expression>)
;;                    |[if-exp (test-exp true-exp false-exp)]|
;;                  | (lambda ({<identifier>}*) <expression>)
;;                    |[lambda-exp (ids body)]|
;;                  | (<expressioni> {<expression>}*)
;;                    |[app-exp (rator rands)]|
;;
;;
; eopl2e, exercise 2.7
; This exercise called for the re-definition of the lex-addr
; function in terms of the define-datatype form.
;
; The following four functions allow us to calculate the lexical
; address of all of the variables within a lambda-calculus
; written according to the above subset of the Scheme grammar.


(define find-in-id-list
  (lambda (id idl posn)
    (cases
     id-list idl
     (empty-id-list () '())
     (non-empty-id-list
      (first-id rest-ids)
      (cond
       ((equal? id first-id) posn)
       (else (find-in-id-list id rest-ids (+ posn 1)) )) ) ) ) )

(define find-lex
  (lambda (id ctx dist)
    (let
        ((posn (cond ((null? ctx) '())
                     (else (find-in-id-list id (car ctx) 0))) ) )
      (cond
       ((null? ctx) (id-free-expr id))
       ((not (null? posn)) (id-bound-expr id dist posn))
       (else (find-lex id (cdr ctx) (+ 1 dist))) ) ) ) )

(define lex-addr-rands
  (lambda (rands ctx)
    (cases
     expr-list rands
     (empty-expr-list () (empty-expr-list))
     (non-empty-expr-list
      (first-expr rest-exprs)
      (non-empty-expr-list
       (lex-addr first-expr ctx)
       (lex-addr-rands rest-exprs ctx)) ) ) ) )

(define lex-addr
  (lambda (e ctx)
    (cases
     lambda-expr e
     (id-expr
      (id)
      (find-lex id ctx 0))
     (const-expr
      (eks)
      (const-expr eks))
     (id-bound-expr
      (id d p)
      (find-lex id ctx 0))
     (id-free-expr
      (id)
      (find-lex id ctx 0))
     (lambda-abst
      (ids body)
      (lambda-abst ids (lex-addr body (cons ids ctx)) ) )
     (if-expr
      (test-expr true-expr false-expr)
      ;; "construct," or derive, an if-expr:
      (if-expr
       (lex-addr test-expr ctx)
       (lex-addr true-expr ctx)
       (lex-addr false-expr ctx)) )
     (appl-expr
      (rator rands)
      (appl-expr
       (lex-addr rator ctx)
       (lex-addr-rands rands ctx))) ) ) )

;; Exercise 2.10
;; Consider the definition of fresh-id:
(define fresh-id-eopl2e-2-10
  (lambda (exp s)
    (let
        ((syms (all-ids exp)))
      (letrec
          ((loop (lambda (n)
                   (let ((sym (string->symbol
                               (string-append s
                                              (number->string n)))))
                     (if (memv sym syms) (loop (+ n 1)) sym) ) ) ) )
        (loop 0) ) ) ) )

;; (define memv-id-expr
;;   (lambda (s-id ids)
;;     (cases
;;      id-list ids
;;      (empty-id-list () #f)
;;      (non-empty-id-list
;;       (hd tl)
;;       (cases
;;        lambda-expr s-id
;;        (id-expr
;;         (id)
;;         (cond ((eqv? id hd) ids)
;;               (else (memv-id-expr s-id tl)) ) )
;;        (else eopl:error 'memv-id-expr "Invalid abstract syntax ~s" s-id) ) ) ) ) )

;; (define memv-id-expr
;;   (lambda (s-id ids)
;;     (cases
;;      id-list ids
;;      (empty-id-list () #f)
;;      (non-empty-id-list
;;       (hd tl)
;;       (cases
;;        identifier hd
;;        (id-i
;;         (i)
;;         (cond ((eqv? s-id hd) ids)
;;               (else (memv-id-expr s-id tl)) ) ) ) )
;;      (else eopl:error 'memv-id-expr "Invalid abstract syntax ~s" ids) ) ) )

(define memv-id-list
  (lambda (s-id ids)
    (cases
     id-list ids
     (empty-id-list () #f)
     (non-empty-id-list
      (hd tl)
      (cond ((equal? s-id hd) ids)
            (else (memv-id-list s-id tl))) )
     (else eopl:error 'memv-id-list "Invalid abstract syntax ~s" ids) ) ) )

(define fresh-id
  (lambda (exp id)
    (let
        ((syms (all-ids exp)))
      (letrec
          ((loop (lambda (n)
                   (let
                       ((sym (id-i (string->symbol
                                    (string-append
                                     id
                                     (number->string n)) ) ) ))
                     (if (memv-id-list sym syms) (loop (+ n 1)) sym) ) ) ) )
        (loop 0) ) ) ) )

;; just like the above, but this time takes the symbol-set
;; as a parameter, instead of calculating it within.
(define fresh-id-s
  (lambda (id syms)
    (letrec
        ((loop (lambda (n)
                 (let
                     ((sym (id-i (string->symbol
                                  (string-append
                                   id
                                   (number->string n)) ) ) ))
                   (if (memv-id-list sym syms) (loop (+ n 1)) sym) ) ) ) )
      (loop 0) ) ) )

(define extract-symbol-string
  (lambda (x)
    (cases
     identifier x
     (id-i
      (i)
      (symbol->string i)) ) ) )

;; Derives an association list, where the "key" is the original
;; variable, and the "data part" is the new version of the variable,
;; as a "fresh id."  This allows us to derive all of the needed
;; "fresh id's" in a single pass, in order to save *some* time!
(define fresh-ids
  (lambda (exp id-l)
    (let ((syms (all-ids exp))) ;; The set-of-all-symbols-in-the-expression
                                ;; is calculated once.
      (letrec
          ((fresher (lambda (ids f-a-list)
                      (cases
                       id-list ids
                       (empty-id-list () f-a-list)
                       (non-empty-id-list
                        (hd tl)
                        (fresher tl (cons (list hd (fresh-id-s (extract-symbol-string hd) syms)) f-a-list)) ) ) ) ) ) 
                        ;; (cons (cons hd (fresh-id-s hd syms)) (fresher tl)) ) ) )) )
        (fresher id-l '()) ) ) ) )
                         

;; Complete the implementation of fresh-id by defining all-ids, which finds
;; all the symbols in a lambda calculus expression (page 48, which is the 
;; much simpler lambda-calculus language of simple appl-expressions,
;; single-variable lambda-expr's, and "naked identifiers.")  This includes
;; the free occurrences, the bound occurrences, and the lambda identifiers
;; for which there are no bound occurrences.

;; This is my first go at it; it's VERY "common-Lispy."
;; Also, this solution is not very efficient, because it simply
;; stuffs symbols into a list, and if the same symbol/name is repeated
;; multiple times inside the expression, named "exp" in the fresh-id
;; function, then it will be repeated in that list.  However, one would
;; hope that the expressions we write would not contain thousands of
;; variables, right?  If so, then we should implemented our "symbol
;; set" using some other kind of associative lookup, such as a hash-table
;; or balanced search tree, to keep performance from deteriorating.

;; (define add-to-set
;;   (lambda (id ss)
;;     (cons id ss) ) )
(define add-to-set
  (lambda (id ss)
    (non-empty-id-list id ss)))

;; (define add-ids-to-set
;;   (lambda (ids ss)
;;     (cond ((null? ids) ss)
;;           (else (add-ids-to-set (cdr ids) (cons (car ids) ss)) ) ) ) )
;; (define add-ids-to-set
;;   (lambda (ids ss)
;;     (cond ((null? ids) ss)
;;           (else (add-ids-to-set (cdr ids)
;;                                 (add-to-set (car ids) ss))) ) ) )
(define add-ids-to-set
  (lambda (ids ss)
    (cases
     id-list ids
     (empty-id-list () ss)
     (non-empty-id-list
      (f-id tl)
      (non-empty-id-list
       f-id
       ss) ) ) ) )

(define add-expr-list-sets
  (lambda (el ss)
    (cases
     expr-list el
     (empty-expr-list () ss)
     (non-empty-expr-list
      (hd tl)
      (let ((intrm-list (all-ids-r hd (empty-id-list))))
        (add-expr-list-sets tl (add-ids-to-set intrm-list ss)) ) ) ) ) )

(define add-id-list-to-set
  (lambda (idl ss)
    (cases
     id-list idl
     (empty-id-list () ss)
     (non-empty-id-list
      (hd tl)
      ;; The calculated "set-of-id's" must be a list
      ;; of things constructed as id-expr's:
      ;; (add-id-list-to-set tl (cons hd ss))) ) ) )
      (add-id-list-to-set tl (add-to-set hd ss)) ) ) ) )

(define all-ids-r
  (lambda (expr sym-set)
    (cases
     lambda-expr expr
     (id-expr
      (id)
      (add-to-set id sym-set))
     (const-expr
      (eks)
      sym-set)
     (lambda-abst
      (idl body)
      (all-ids-r body (add-id-list-to-set idl sym-set)) )
     (if-expr
      (test-expr true-expr false-expr)
      (all-ids-r
       test-expr
       (all-ids-r
        true-expr
        (all-ids-r
         false-expr
         sym-set))))
     (appl-expr
      (rator rands)
      (all-ids-r
       rator
       (add-expr-list-sets rands sym-set)))
     (else (eopl:error 'all-ids-r
                       "Invalid concrete syntax ~s" expr) ) ) ) )

(define all-ids
  (lambda (e)
    (all-ids-r e (empty-id-list))))


;; (lex-addr
;;  '(lambda (a b c)
;;     (if (eqv? b c)
;;         ((lambda (c) (cons a c)) a)
;;         b ) )
;;   '())

;; (lex-addr '(func ((lambda (p q) (f p ((lambda (q) (f1 q r)) q))) m n) ) '())

;; (unparse-lambda-expr
;;  (appl-expr
;;   (lambda-abst
;;    (non-empty-id-list 'w2 (empty-id-list))
;;    ;; eopl2e said the following, in their book-example
;;    ;; in exercise 2.10, but I don't think they mean to say
;;    ;; it:
;;    ;;   'w2
;;    ;; This is mistaken because the single symbol is not within
;;    ;; a list, which is implied by the concrete syntax, even
;;    ;; if their abstract syntax doesn't make it explicit.
;;    ;; But they're trying to give you a variable which is not
;;    ;; free, and not bound, either.  
;;    (appl-expr (id-expr 'w1) (non-empty-expr-list (id-expr 'w0) (empty-expr-list))) )
;;   (non-empty-expr-list (id-expr 'w3) (empty-expr-list))) )

;; There are four kinds of variables:
;; free only
;; bound only
;; free and bound at the same time
;;   (i.e., there are places in the expression where the variable
;;   occurs free, and others in which it occurs bound...)
;; not free AND not bound
;;   (i.e., the variable occurs in a lambda-abstraction's parameter list,
;;   but it is not used anywhere in the lambda body!)

;; (parse-lambda-expr '((lambda (w2) (w1 w0)) w3))

;; (unparse-lambda-expr
;;  (lex-addr
;;   (parse-lambda-expr '((lambda (w2) (w1 w0)) w3))
;;   '()))

;; (occurs-free? 'w2 (parse-lambda-expr '((lambda (w2) (w1 w0)) w3)))
;; (occurs-bound? 'w2 (parse-lambda-expr '((lambda (w2) (w1 w0)) w3)))
;; Both of the above should return #f!  Seems strange, but it makes
;; sense after you try to think about it for a bit.
;; Such variables are important, for they allow you to write a
;; function which throws away arguments, right?

;; exercise 2.11
;; Extended the grammar/datatype above to include general strings,
;; numbers, and booleans as available in Scheme itself.
;; That way, we can consider substituting (* p 3) for x in
;;   (lambda (p) (+ p x))
;; and
;;   (lambda (q) (+ q x))
;; to result in:
;;   (lambda (p) (+ p (* p 3)))
;; and
;;   (lambda (q) (+ q (* p 3)))
;; Now that obviously highlights the problem of variable capture, eh?
;; See how, in the first expression, (lambda (p) (+ p x))
;; the use of p in (* p 3) means that p "got captured" and is now
;; bound.  The same is NOT true of the second expression, right?
;; 
;; eopl2e continues by saying:
;; "We can fix this problem by renaming the bound variable to some
;; fresh name, say p0, so the result of the substitution becomes
;;   (lambda (p0) (+ p0 (* p 3)))
;; Capture is thereby avoided; it no longer matters whether the
;; original bound variable was p or q.  Here is the notation we use
;; for this throughout:
;;   E1[E2/x]
;; The resultant expression is the same as E1 with free occurrences
;; of the identifier x replaced by the expression E2."
;;
;; "Below is the definition of a procedure that substitutes subst-exp
;; for all occurrences of subst-id in exp, but without renaming."
;;
;; (define lambda-calculus-subst
;;   (lambda (exp subst-exp subst-id)
;;     ;; i.e., compute exp[subst-exp/subst-id]
;;     (letrec
;;         ((subst
;;           (lambda (exp)
;;             (cases
;;              expression exp
;;              (var-exp
;;               (id)
;;               (if (eqv? id subst-id) subst-exp exp))
;;              (lambda-exp
;;               (id body)
;;               (if (eqv? id subst-id)
;;                   exp
;;                   (lambda-exp id (subst body))))
;;              (app-exp
;;               (rator rand)
;;               (app-exp (subst rator) (subst rand)))
;;              (lit-exp
;;               (datum)
;;               (lit-exp datum))
;;              (primapp-exp
;;               (prim rand1 rand2)
;;               (primapp-exp prim (subst rand1) (subst rand2)))) ) ) )
;;       (subst exp) ) ) )
;;
;; "Fix lambda-calculus-subst so that it performs renaming when necessary.
;; Hint:  use fresh-id from the previous exercise."
;; 
;; Had to extend the above grammar a bit, right?
;; But only needed to add a catch-all "const-expr" variant to the
;; grammar in question.



;; Started out with the "skeletal" version of the wretched thing,
;; 
(define lambda-calculus-subst
  (lambda (exp       ;; The expression which must be changed.
           subst-exp ;; The expression which will be "plugged into" exp 
           subst-id) ;; The identifier inside of exp which will be replaced by subst-exp
    ;; i.e., this is supposed to calculate 
    ;;   exp[subst-exp/subst-id]
    ;; AND avoid variable capture!
    (let
        ;; Seems to me that we need to know what the ids are inside subst-exp
        ;; so that we can check to see if any bound id's we find in exp are
        ;; a match for an id in the subst-exp?
        ( (se-ids (all-ids subst-exp)) )
      (letrec
          ((subst
            (lambda (exp)
              (cases
               lambda-expr exp
               (const-expr (eks) eks)
               (id-expr
                (id)
                (cond ((equal? id subst-id) subst-exp)
                      (else id)))
               (lambda-abst
                (ids body)
                (let ((iset (id-list-intersection ids se-ids)))
                  (cond
                   ;; If there are NOT any id's in common between the argument list of this lambda,
                   ;; then we must merely recursively substitute, as usual.
                   ((null? iset)
                    (lambda-expr ids (subst body)))
                   ;; Otherwise, we must perform a set up substitutions on the lambda's body:
                   ;; replace every free occurrence of a variable in the iset with its counterpart:
                   (else
                    (lambda-expr
                     ids
                     ;; We need to use the "fresh" version of:  the identifier from the ids set
                     ;; which also appears in the se-ids set.
                     (subst (lambda-calculus-subst body (id-expr (caar iset)) (fresh-ids body )) ) ) ) ) ) )
               (if-expr
                (test-expr true-expr false-expr)
                (if-expr (subst test-expr) (subst true-expr) (subst false-expr)))
               (appl-expr
                (rator rands)
                (appl-expr
                 (subst rator)
                 (expr-list-subst rands subst-exp subst-id)))
               (else (eopl:error 'lambda-calculus-subst
                                 "Invalid abstract syntax ~s" exp) ) ) ) ))
        (subst exp) ) ) ) ) )

;; (define rec-subst
;;   (lambda (exp
;;            subst-exp
;;            subst-ids)
;;     (let
;;         ( (se-ids (all-ids subst-exp)) )
;;       (letrec
;;           ((subst
;;             (lambda (exp)
;;               (cases
;;                lambda-expr exp
;;                (const-expr (eks) exp)
;;                (id-expr
;;                 (id)
;;                 ; replace id with its substitution, if needed.
;;                 (id-expr (subst-from-list id subst-ids)) )
;;                (lambda-abst
;;                 (ids body)
;;                 (let
;;                     ((iset (id-list-intersection ids se-ids)))
;;                   ((null? iset)
;;                    (lambda-expr
;;                     ids
;;                     (subst body)))
;;                   (else
;;                    (lambda-expr
;;                     ids
;;                     (subst
;;                      (rec-subst body 
                    
;; This might be useful later, to execute a substitution
;; later.
(define subst-from-list
  (lambda (i sil)
    (cond
     ((null? sil) i)
     ((equal? i (caar sil)) (cdar sil))
     (else (subst-from-list i (cdr sil) ) ) ) ) )

;; NOT SURE THIS IS NEEDED ANYMORE, SINCE THE memv-id-list
;; HAS KIND OF TAKEN OVER FOR IT?
(define in-id-list?
  (lambda (item idl)
    (cases
     id-list idl
     (empty-id-list () #f)
     (non-empty-id-list
      (first-id rest-ids)
      (cond ((equal? first-id item) #t)
            (else (in-id-list? item rest-ids)) )) ) ) )

;; A tool to calculate the set of symbols which appear
;; in both the idl AND the sym-set.  Uses the straightforward,
;; naive techniques for now.
;; If an item from idl appears at least once in sym-set, then
;; it will appear in the resulting set, calculated as iset.
(define id-list-intersection-r
  (lambda (idl sym-set iset)
    (cases
     id-list idl
     (empty-id-list () iset)
     (non-empty-id-list
      (hd tl)
      (cond ((memv-id-list hd sym-set)
             (id-list-intersection-r tl sym-set (add-to-set hd iset)) )
            (else (id-list-intersection-r tl sym-set iset)) ) ) ) ) )

(define id-list-intersection
  (lambda (idl sym-set)
    (id-list-intersection-r idl sym-set (empty-id-list))))

(define id-list-head
  (lambda (idl)
    (cases
     id-list idl
     (non-empty-id-list
      (hd tl)
      hd)
     (else eopl:error 'id-list-head "Invalid option ~s" idl) ) ) )
     (empty-id-list () idl)
     (