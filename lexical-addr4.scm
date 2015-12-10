;; Preparatory steps:
(load "eopl2e/code/interps/r5rs.scm")
(load "eopl2e/code/interps/define-datatype.scm")

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
(define-datatype id-list id-list?
  (empty-id-list)
  (non-empty-id-list
   (first-id symbol?)
   (rest-ids id-list?)))

;; (define-datatype expr-list expr-list?
;;   (an-expr-list (expr-list-data (genl-list-of lambda-expr?)) ) )
(define-datatype expr-list expr-list?
  (empty-expr-list)
  (non-empty-expr-list
   (first-expr lambda-expr?)
   (rest-exprs expr-list?) ) )

(define-datatype lambda-expr lambda-expr?
  (id-expr
   (identifier symbol?))
  ;; The following two variants are useful for representing
  ;; "lexically addressed" identifiers:
  (id-bound-expr
   (identifier symbol?)
   (lex-id-dist number?)
   (lex-id-posn number?))
  (id-free-expr
   (identifier symbol?))
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
           (non-empty-id-list (car x)
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
     ((symbol? datum) (id-expr datum))
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
      (cons first-id (unparse-ids rest-ids))) ) ) )

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
     (id-expr (identifier) identifier)
     ;;
     ;; Two cases to handle the cases of identifiers
     ;; "decorated" with lexical depth information
     (id-bound-expr (id d p) (list id ': d p))
     (id-free-expr (id) (list 'free id))
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
    (cases id-list ids
           (empty-id-list () #f)
           (non-empty-id-list
            (first-id rest-ids)
            (or (eqv? x first-id)
                (occurs-in x rest-ids))))))

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
            (identifier)
            (eqv? x identifier))
           ;;
           (id-bound-expr
            (id d p)
            (eqv? x id))
           (id-free-expr
            (id)
            (eqv? x id))
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
            (or (and (occurs-in x ids) (occurs-free? x body))
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
  (lambda (e ctx) ; ctx is always a list of, lists of vars from the enclosing context(s).
    (cases
     lambda-expr e
     (id-expr
      (identifier)
      (find-lex identifier ctx 0)) ; start looking for the variable within the stack of contexts.
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

(define all-ids-ids
  (lambda (ids)
    (cases
        id-list ids
      (empty-id-list () '())
      (non-empty-id-list
       (first-id rest-ids)
       (cons first-id (all-ids-ids rest-ids)) )
      )
    )
  )

(define all-ids-expr-list
  (lambda (rands)
    (cases
        expr-list rands
      (empty-expr-list () '())
      (non-empty-expr-list
       (first-expr rest-exprs)
       (append (all-ids first-expr)
               (all-ids-expr-list rest-exprs)) )
      )
    )
  )

(define all-ids
  (lambda (lce)
    (cases
        lambda-expr lce
      (id-expr (identifier) (list identifier))
      (id-bound-expr (id d p) (list id))
      (id-free-expr (id) (list id))
      ;;
      (lambda-abst
       (ids body)
       (append (all-ids-ids ids) (all-ids body)) )
      ;;
      (if-expr
       (test-expr true-expr false-expr)
       (append (all-ids test-expr)
               (all-ids true-expr)
               (all-ids false-expr)) )
      ;;
      (appl-expr
       (rator rands)
       (append (all-ids rator)
               (all-ids-expr-list rands)) ) )
    )
  )


;; (lex-addr
;;  '(lambda (a b c)
;;     (if (eqv? b c)
;;         ((lambda (c) (cons a c)) a)
;;         b ) )
;;   '())

;; (lex-addr '(func ((lambda (p q) (f p ((lambda (q) (f1 q r)) q))) m n) ) '())

(unparse-lambda-expr
 (appl-expr
  (lambda-abst
   (non-empty-id-list 'w2 (empty-id-list))
   ;; eopl2e said the following, in their book-example
   ;; in exercise 2.10, but I don't think they mean to say
   ;; it:
   ;;   'w2
   ;; This is mistaken because the single symbol is not within
   ;; a list, which is implied by the concrete syntax, even
   ;; if their abstract syntax doesn't make it explicit.
   ;; But they're trying to give you a variable which is not
   ;; free, and not bound, either.  
   (appl-expr (id-expr 'w1) (non-empty-expr-list (id-expr 'w0) (empty-expr-list))) )
  (non-empty-expr-list (id-expr 'w3) (empty-expr-list))) )

;; There are four kinds of variables:
;; free only
;; bound only
;; free and bound at the same time
;;   (i.e., there are places in the expression where the variable
;;   occurs free, and others in which it occurs bound...)
;; not free AND not bound
;;   (i.e., the variable occurs in a lambda-abstraction's parameter list,
;;   but it is not used anywhere in the lambda body!)

(parse-lambda-expr '((lambda (w2) (w1 w0)) w3))

(unparse-lambda-expr
 (lex-addr
  (parse-lambda-expr '((lambda (w2) (w1 w0)) w3))
  '()))

(occurs-free? 'w2 (parse-lambda-expr '((lambda (w2) (w1 w0)) w3)))
(occurs-bound? 'w2 (parse-lambda-expr '((lambda (w2) (w1 w0)) w3)))
;; Both of the above should return #f!  Seems strange, but it makes
;; sense after you try to think about it for a bit.
;; Such variables are important, for they allow you to write a
;; function which throws away arguments, right?

