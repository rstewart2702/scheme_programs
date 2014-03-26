;; Preparatory steps:
; (primitive-load "eopl2e/code/interps/r5rs.scm")
; (primitive-load "eopl2e/code/interps/define-datatype.scm")

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
(define-datatype lambda-expr lambda-expr?
  (id-expr
   (identifier symbol?))
  (lambda-abst ;; "lambda abstraction?"
   (ids id-list?)
   ;; (ids (genl-list-of symbol?))
   (body lambda-expr?))
  (if-expr
   (test-expr lambda-expr?)
   (true-expr lambda-expr?)
   (false-expr lambda-expr?))
  (appl-expr
   (rator lambda-expr?)
   (rands expr-list?) ) )

(define genl-list-of
  (lambda (pred)
    (lambda (val)
      (or (null? val)
          (and (pair? val)
               (pred (car val))
               ((genl-list-of pred) (cdr val)) ) ) ) ) )

(define-datatype id-list id-list?
  (an-id-list
   (id-list-data (genl-list-of symbol?)) ) )

(define-datatype expr-list expr-list?
  (an-expr-list
   (expr-list-data (genl-list-of lambda-expr?)) ) )

;; We MUST be able to calculate an abstract-syntax-tree version of
;; lambda-expr's, and that is the purpose of this function:
(define parse-le-id-list
  (lambda (x)
    (cond ((null? x) '())
          ;; (else (cons (parse-lambda-expr (car x))
          (else (cons (car x)
                      (parse-le-id-list (cdr x)))))))
    ;; (cond ((null? x) '())
    ;;       (else
    ;;        (non-empty-id-list (car x)
    ;;                           (parse-le-id-list (cdr x)))))))

(define parse-le-expr-list
  (lambda (x)
    (cond ((null? x) '())
          (else (cons (parse-lambda-expr (car x))
                      (parse-le-expr-list (cdr x)))))))
    ;; (cond ((null? x) (empty-expr-list))
    ;;       (else
    ;;        (non-empty-expr-list (parse-lambda-expr (car x))
    ;;                             (parse-le-expr-list (cdr x)))))))

(define parse-lambda-expr
  (lambda (datum)
    (cond
     ((symbol? datum) (id-expr datum))
     ((pair? datum)
      (cond
       ((and (symbol? (car datum))
             (eqv? 'lambda (car datum)))
        (lambda-abst
         (an-id-list (parse-le-id-list (cadr datum)))
         ;; (an-id-list (cadr datum))
         ;; (an-expr-list (parse-lambda-expr  (caddr datum)))) )
         ;; (an-expr-list (parse-le-expr-list (caddr datum)))) )
         (parse-lambda-expr (caddr datum) ) ) ) 
       ((and (symbol? (car datum))
             (eqv? 'if (car datum)))
        (if-expr
         (parse-lambda-expr (cadr datum))
         (parse-lambda-expr (caddr datum))
         (parse-lambda-expr (cadddr datum))) )
       (else
        (appl-expr
         (parse-lambda-expr (car datum))
         (an-expr-list (parse-le-expr-list (cdr datum)) ) ) ) ) )
     (else (eopl:error 'parse-lambda-expr
                       "Invalid concrete syntax ~s" datum)))))

  

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

;; THIS WON'T WORK PROPERLY, BECAUSE OF THE DECISION IN THE ABOVE
;; CODE TO USE SCHEME'S BUILT-IN LIST STRUCTURE AS THE ABSTRACT
;; SYNTAX FOR LISTS OF IDENTIFIERS.  THIS MEANS THAT THE occurs-in
;; HELPER FUNCTION MUST BE A SHELL/WRAPPER AROUND A RECURSIVE CHECK
;; OF THE NAKED LIST OF SYMBOLS, IMPLEMENTED AS A "NATIVE SCHEME FUNCTION."
;; HOPPING BETWEEN LEVELS OF ABSTRACTION IN ALL OF THESE NON-UNIFORM WAYS
;; IS CONFUSING, TO ME, ANYWAY.
;;
;; THE occurs-in-old SHOWS THE "BROKEN" FUNCTION, AND THE occurs-in
;; FUNCTION SHOWS THE FUNCTION WHICH IS CORRECT, WHICH WILL "UNPACK"
;; OR "UNWRAP" THE IDENTIFIER-LIST STRUCTURE WHICH IS A SCHEME LIST.
;;
;; THE SAME KIND OF "UNPACKING" IS NEEDED IN THE DEFINITION OF THE
;; occurs-free-helper FUNCTION.  SIGH.
(define occurs-in-old
  (lambda (x ids)
    (cases id-list ids
           (an-id-list
            (id-list-data)
            (cond ((null? id-list-data) #f)
                  (else (or (eqv? x (car id-list-data))
                            (occurs-in-old x (cdr id-list-data)))))))))
(define occurs-in
  (lambda (x ids)
    (letrec
        ((occurs-in-helper
          (lambda (x xs)
            (cond ((null? xs) #f)
                  (else (or (eqv? x (car xs))
                            (occurs-in-helper x (cdr xs))))))))
      (cases id-list ids
             (an-id-list
              (id-list-data)
              (occurs-in-helper x id-list-data) ) ) ) ) )

;; (define occurs-free-helper
;;   (lambda (x rands)
;;     (cond ((null? rands) #f)
;;           ((occurs-free? x (car rands))

(define occurs-free-helper-old
  (lambda (x rands)
    (cases expr-list rands
           (an-expr-list
            (e-list)
            (cond ((null? e-list) #f)
                  (else (or (occurs-free? x (car e-list))
                            (occurs-free-helper-old x (cdr e-list)) )))))))
(define occurs-free-helper
  (lambda (x rands)
    (letrec
        ((occurs-free-in-helper
          (lambda (x xs)
            (cond ((null? xs) #f)
                  (else (or (occurs-free? x (car xs))
                            (occurs-free-in-helper x (cdr xs))))))))
      (cases expr-list rands
             (an-expr-list
              (e-list)
              (occurs-free-in-helper x e-list))))))

(define occurs-free?
  (lambda (x E)
    (cases lambda-expr E
           (id-expr
            (identifier)
            (eqv? x identifier))
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
    (cases
     lambda-expr E
     (id-expr
      (identifier)
      #f)
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

(define occurs-bound-helper-old
  (lambda (x rands)
    (cases expr-list rands
           (an-expr-list
            (e-list)
            (cond ((null? e-list) #f)
                  (else (or (occurs-bound? x (car e-list))
                            (occurs-bound-helper-old x (cdr e-list)))))))))
(define occurs-bound-helper
  (lambda (x rands)
    (letrec
        ((occurs-bound-in-helper
          (lambda (x xs)
            (cond ((null? xs) #f)
                  (else (or (occurs-bound? x (car xs))
                            (occurs-bound-in-helper x (cdr xs))))))))
      (cases expr-list rands
             (an-expr-list
              (e-list)
              (occurs-bound-in-helper x e-list))))))

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
; The following three functions allow us to calculate the lexical
; address of all of the variables within a lambda-calculus
; written according to the above subset of the Scheme grammar.


; Calculate the lexical address given a lexical context:
(define find-in
  (lambda (sym lst n)
    (cond ((null? lst) '())
          ((eqv? sym (car lst)) n)
          (else (find-in sym (cdr lst) (+ n 1))) ) ) )

; Calculates the lexical address of a symbol sym
; given the present context ctx and "depth" d
(define find-lex
  (lambda (sym ctx d)
    (let ((p (cond ((null? ctx) '())
                   (else (find-in sym (car ctx) 0)) ) ) )
      (cond ((null? ctx) (list sym 'free))
            ((null? p) (find-lex sym (cdr ctx) (+ d 1)))
            (else (list sym ': d p)) ) ) ) )

(define lex-addr
  (lambda (e ctx)
    (cond ((null? e) '())
          ((symbol? e) (find-lex e ctx 0))
          ((eqv? (car e) 'lambda)
             (list 'lambda (cadr e) (lex-addr (caddr e) (cons (cadr e) ctx) ) ) )
          ((eqv? (car e) 'if)
             (list 'if
                   (lex-addr (cadr e) ctx)
                   (lex-addr (caddr e) ctx)
                   (lex-addr (cadddr e) ctx) ) )
          ((list? e) (cons (lex-addr (car e) ctx) (lex-addr (cdr e) ctx)) ) ) ) )

;; (lex-addr
;;  '(lambda (a b c)
;;     (if (eqv? b c)
;;         ((lambda (c) (cons a c)) a)
;;         b ) )
;;   '())

;; (lex-addr '(func ((lambda (p q) (f p ((lambda (q) (f1 q r)) q))) m n) ) '())

