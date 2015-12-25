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

(define list-of
  (lambda (pred)
    (lambda (l)
      (cond ((null? l) #t)
            (else (and (pred (car l))
                       ((list-of pred) (cdr l)) )) ) ) ) )

;; First, the abstract syntax for the lambda-calculus grammar
;; above:
(define-datatype identifier id?
  (id-i
   (i symbol?)) )

(define-datatype id-list id-list?
  (empty-id-list)
  (non-empty-id-list
   (first-id id?)
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
   (id symbol?))
  ;; The following two variants are useful for representing
  ;; "lexically addressed" identifiers:
  (id-bound-expr
   (id symbol?)
   (lex-id-dist number?)
   (lex-id-posn number?))
  (id-free-expr
   (id symbol?))
  ;;
  (lambda-abst ;; "lambda abstraction?"
   (ids (list-of symbol?))
   (body lambda-expr?))
  (if-expr
   (test-expr lambda-expr?)
   (true-expr lambda-expr?)
   (false-expr lambda-expr?))
  (appl-expr
   (rator lambda-expr?)
   (rands (list-of lambda-expr?)) ) )

;; We MUST be able to calculate an abstract-syntax-tree version of
;; lambda-expr's, and that is the purpose of this function:
;; (define parse-le-id-list
;;   (lambda (x)
;;     (cond ((null? x) (empty-id-list))
;;           (else
;;            (non-empty-id-list (id-i (car x))
;;                               (parse-le-id-list (cdr x)))))))

(define parse-le-expr-list
  (lambda (x)
    (cond ((null? x) '())
          (else
           (cons (parse-lambda-expr (car x))
                 (parse-le-expr-list (cdr x)))))))

(define parse-lambda-expr
  (lambda (datum)
    (cond
     ((const? datum) (const-expr datum))
     ((symbol? datum) (id-expr datum))
     ((pair? datum)
      (cond
       ((and (symbol? (car datum))
             (eqv? 'lambda (car datum)))
        (let ((arg-list (cadr datum))
              (body-expr (caddr datum)) )
          (lambda-abst
           arg-list
           (parse-lambda-expr body-expr)) ) )
       ((and (symbol? (car datum))
             (eqv? 'if (car datum)))
        (let ((test-expr (cadr datum))
              (true-expr (caddr datum))
              (false-expr (cadddr datum)))
          (if-expr
           (parse-lambda-expr test-expr)
           (parse-lambda-expr true-expr)
           (parse-lambda-expr false-expr)) ) )
       (else
        (let ((rator-expr (car datum))
              (rands-list (cdr datum)) )
          (appl-expr
           (parse-lambda-expr rator-expr)
           (parse-le-expr-list rands-list) ) ) ) ) )
     (else (eopl:error 'parse-lambda-expr
                       "Invalid concrete syntax ~s" datum)))))

(define unparse-expr-list
  (lambda (rands)
    (cond ((null? rands) '())
          (else (cons (unparse-lambda-expr (car rands))
                      (unparse-expr-list (cdr rands)) ) ) ) ) )

(define unparse-lambda-expr
  (lambda (ast)
    (cases
     lambda-expr ast
     (id-expr (id) id)
     (const-expr (eks) eks)
     ;;
     ;; Two cases to handle the cases of identifiers
     ;; "decorated" with lexical depth information
     (id-bound-expr
      (id d p)
      (list id ': d p))
     (id-free-expr
      (id)
      (list 'free id) )
     ;;
     (lambda-abst
      (ids body)
      (list
       'lambda
       ids 
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

;; For brevity's sake, this should probably be eliminated,
;; but I'll leave it in for now:
(define occurs-in
  (lambda (x ids)
    (cond ((memv x ids) #t)
          (else #f) ) ) )

;; (define occurs-free-helper
;;   (lambda (x rands)
;;     (cond ((null? rands) #f)
;;           ((occurs-free? x (car rands))

(define occurs-free-helper
  (lambda (x rands)
    (cond ((null? rands) #f)
          (else (or (occurs-free? x (car rands))
                    (occurs-free-helper x (cdr rands))) ) ) ) )

(define occurs-free?
  (lambda (x E)
    (cases lambda-expr E
           (id-expr
            (id)
            (eqv? x id))
           (const-expr
            (eks)
            #f)
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
            (or (occurs-free? x body)
                (occurs-bound? x body)))
           ;;
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
    (cond ((null? rands) #f)
          (else (or (occurs-bound? x (car rands))
                    (occurs-bound-helper x (cdr rands)))))))

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
    (cond ((null? idl) '())
          ((equal? id (car idl)) posn)
          (else (find-in-id-list id (cdr idl) (+ posn 1))))))

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
    (cond ((null? rands) '())
          (else (cons (lex-addr (car rands) ctx)
                      (lex-addr-rands (cdr rands) ctx)) ) ) ) )

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
                     ((sym (string->symbol
                            (string-append
                             id
                             (number->string n)) ) ))
                   (if (memv sym syms) (loop (+ n 1)) sym) ) ) ) )
      (loop 0) ) ) )

(define extract-symbol-string
  (lambda (x) (symbol->string x)))

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
                      (cond ((null? ids) f-a-list)
                            (else
                             (fresher
                              (cdr ids)
                              (cons
                               (list
                                (car ids)
                                (fresh-id-s
                                 (extract-symbol-string (car ids)) syms))
                               f-a-list)) ) ) ) ) )
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

(define add-to-set
  (lambda (id ss)
    (cons id ss)))

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
    (cond ((null? ids) ss)
          (else (add-ids-to-set
                 (cdr ids)
                 (cons (car ids) ss)) ) ) ) )

(define add-expr-list-sets
  (lambda (el ss)
    (cond ((null? el) ss)
          (else (let ((intrm-list (all-ids-r (car el) '())))
                  (add-expr-list-sets
                   (cdr el)
                   (add-ids-to-set intrm-list ss)) ) ) ) ) )

(define add-id-list-to-set
  (lambda (idl ss)
    (cond ((null? idl) ss)
          (else (add-id-list-to-set (cdr idl) (cons (car idl) ss))) ) ) )

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
    (all-ids-r e '()) ) )


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



;; This is a departure from what was asked for in the textbook, for it
;; works with the lambda-calculus language above which permits multiple
;; arguments for lambda-abst's, which meant working out what it means
;; for multiple 
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
               ;; In this variant, there's nothing to do, so the result
               ;; should be the expression, unchanged.
               ;; The return-expression could be (const-expr eks),
               ;; but that just imposes more overhead, eh?
               (const-expr (eks) exp)
               (id-expr
                (id)
                (cond ((equal? id subst-id) subst-exp)
                      (else exp)))
               (lambda-abst
                (ids body)
                ;; Originally, I had thought that there would be
                ;; unnecessary variable renaming, because
                ;; a bound variable in the exp would be renamed
                ;; if it happens to show up in the se-ids.
                ;; But this renaming is necessary if the subst-exp
                ;; happens to be an expression which contains bound
                ;; occurrences of the subst-id, yes?  NO!  It *still is not necessary!*
                ;; So, we must
                ;; always be sure to perform the renaming if there
                ;; are bound occurrences of any of the se-ids
                ;; in the list of parameters used by the exp, which
                ;; happens to be a lambda-abst, in this case.
                (let ((iset (id-list-intersection
                             ids
                             se-ids) ) )
                  ;; iset is the set-of-id's-which are in both the arg-list and the subst-expr.
                  ;; 
                  (cond
                   ;; If there are NOT any id's in common between the argument list of this lambda,
                   ;; and the id's which occur in the subst-exp,
                   ;; then we must merely recursively substitute, as usual.
                   ((and (null? iset)
                         ; Don't understand the need to check that
                         ; subst-id is not bound in exp?
                         ; RIGHT!  We don't want to have to rename
                         ; a variable in the exp that happens to be
                         ; bound in exp, the target expression, correct?
                         (not (occurs-bound? subst-id exp))
                         )
                    (lambda-abst ids (subst body)))
                   ;; Otherwise, we must perform a set up substitutions on the lambda's body:
                   ;; replace every occurrence of a variable in the ids with a new counterpart:
                   (else
                    ;; All of the id's in the parameter list must be renamed.
                    ;; This renaming is necessary, even when (occurs-bound? subst-id exp).
                    ;; Even if there are not any id's common between the subst-exp
                    ;; and the parameter list, if the subst-id is bound in the
                    ;; exp (which is a lambda-abst in this case) it must be renamed
                    ;; so that the recursive call to subst, below, does not
                    ;; substitute the subst-exp for the bound variable named by
                    ;; subst-id.
                    ;;
                    ;; 2015-12-09 we don't really need to rename ALL of the bound
                    ;; variables in exp, just the ones which are also used in the
                    ;; subst-expr, right?  But currently, this renames all of them.
                    ;; Oh!  Not anymore, once I changed ids to iset below in the
                    ;; definition of fresh-list.
                    ;;
                    ;; Need to rename all identifiers inside exp which also
                    ;; happen to be identifiers within the subst-exp.
                    ;; This is done partly to avoid variable capture,
                    ;; but also to help allay confusion.  In other words,
                    ;; not all of the bound-identifier-renaming done here is
                    ;; is necessary to preserve correctness.
                    (let
                        ((fresh-list (fresh-ids body iset)) )
                      (lambda-abst
                       (replace-ids ids fresh-list)
                       (subst (lambda-subst-helper body fresh-list)) ) ) ) ) ) )
               (if-expr
                (test-expr true-expr false-expr)
                (if-expr (subst test-expr) (subst true-expr) (subst false-expr)))
               (appl-expr
                (rator rands)
                (appl-expr
                 (subst rator)
                 (expr-list-subst subst rands)))
               (else (eopl:error 'lambda-calculus-subst
                                 "Invalid abstract syntax ~s" exp) ) ) ) ))
        (subst exp) ) ) ) )

(define lambda-calculus-subst2
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
               (const-expr (eks) exp)
               (id-expr
                (id)
                (cond ((equal? id subst-id) subst-exp)
                      (else exp)))
               (lambda-abst
                (arg-list body)
                (let ((iset (id-list-intersection
                             arg-list
                             se-ids) ) )
                  ;; iset is the set-of-id's-which are in both the arg-list and the subst-expr.
                  ;;
                  (display iset)(display "\n")
                  (display (unparse-lambda-expr exp))(display "\n")
                  (display arg-list)(display "\n")
                  (display se-ids)(display "\n")
                  (display subst-id)(display "\n")
                  (display (member subst-id arg-list))(display "\n\n")
                  (cond
                   ;; If there are NOT any id's in common
                   ;; between the argument list of this lambda,
                   ;; and the id's which occur in the subst-exp,
                   ;; and the the identifier which is being replaced
                   ;; is not already bound in the target expression, exp,
                   ;; then we must merely recursively substitute, as usual.
                   (;; (and (null? iset)
                    ;;      (not (occurs-bound? subst-id exp))
                    ;;      )
                    (and (null? iset)
                         (not (member subst-id arg-list)) )
                  (display "first clause\n")
                  (display iset)(display "\n")
                  (display (unparse-lambda-expr exp))(display "\n")
                  (display arg-list)(display "\n")
                  (display se-ids)(display "\n")
                  (display subst-id)(display "\n\n")
                    (lambda-abst arg-list (subst body)))
                   ;; Otherwise, we must perform a set up substitutions on the lambda's body:
                   ;; replace every occurrence of a variable in the ids with a new counterpart:
                   (else
                    (let*
                        ((fresh-list (fresh-ids body iset))
                         (la-result (lambda-abst (replace-ids arg-list fresh-list) (subst (lambda-subst-helper2 body fresh-list)))) )
                      (display (unparse-lambda-expr exp))(display "\n")
                      (display (unparse-lambda-expr la-result))(display "\n\n")
                      la-result
;                      (lambda-abst
;                       (replace-ids arg-list fresh-list)
;                       (subst (lambda-subst-helper body fresh-list)) )
                      ) ) ) ) )
               (if-expr
                (test-expr true-expr false-expr)
                (if-expr (subst test-expr) (subst true-expr) (subst false-expr)))
               (appl-expr
                (rator rands)
                (appl-expr
                 (subst rator)
                 (expr-list-subst subst rands)))
               (else (eopl:error 'lambda-calculus-subst
                                 "Invalid abstract syntax ~s" exp) ) ) ) ))
        (subst exp) ) ) ) )


(define lambda-calculus-subst3
  (lambda (exp       ;; The expr which must be changed.
           subst-exp ;; The expr which will be "plugged into" exp 
           subst-id) ;; The identifier inside of exp which will be
                     ;;   replaced by subst-exp
    ;; i.e., this is supposed to calculate 
    ;;   exp[subst-exp/subst-id]
    ;; AND avoid variable capture!
    (let
        ;; Seems to me that we need to know what the ids
        ;; are inside subst-exp so that we can check to see
        ;; if any bound id's we find in exp are
        ;; a match for an id in the subst-exp?
        ( (se-ids (all-ids subst-exp)) )
      (letrec
          ((subst
            (lambda (exp)
              (cases
               lambda-expr exp
               (const-expr (eks) exp)
               (id-expr
                (id)
                (cond ((equal? id subst-id) subst-exp)
                      (else exp)))
               (lambda-abst
                (arg-list body)
                ;; iset is the set-of-id's-which are in both
                ;; the arg-list and the subst-expr.
                ;;
                (cond
                  ;; If the subst-id is in the arg-list,
                  ;; then it's a bound var in exp
                  ;; and no substitution is allowed or needed.
                  ((memv subst-id arg-list) exp)
                  ;; If there are identifiers in common between
                  ;; the arg-list and the identifiers used in
                  ;; the subst-expr, then we must rename the
                  ;; common identifier instances inside the
                  ;; arg-list and the body of the exp
                  ;; (which is a lambda-abst) and the
                  ;; substitution must be performed on the
                  ;; new version of the lambda-abst.
                  (else
                   (let
                       ((iset (id-list-intersection arg-list se-ids) ))
                     (cond
                       ((not (null? iset))
                        (let*
                            ((fresh-list (fresh-ids body iset))
                             (new-lambda-abst
                              (lambda-abst
                               (replace-ids arg-list fresh-list)
                               (lambda-subst-helper3 body fresh-list) ) ) )
                          (subst new-lambda-abst) ) )
                       ;; If there weren't any identifiers in
                       ;; common between the arg-list and the
                       ;; identifiers used in the subst-expr,
                       ;; then all that is necessary is to
                       ;; calculate the substitution
                       ;; on the lambda-abst's body.
                       ((null? iset)
                        (lambda-abst arg-list (subst body)) ) ) ) ) ) )
                (if-expr
                 (test-expr true-expr false-expr)
                 (if-expr (subst test-expr) (subst true-expr) (subst false-expr)))
                (appl-expr
                 (rator rands)
                 (appl-expr
                  (subst rator)
                  (expr-list-subst subst rands)))
                (else (eopl:error 'lambda-calculus-subst3
                                  "Invalid abstract syntax ~s" exp) ) ) ) ) )
           (subst exp) ) ) ) )

;; *****************************************************
;; Help with processing (<identifier> <subst-expr>) pairings?
;; This is with an eye towards building infrastructure to help us
;; with such lists, yes?
;;
;; We want something which does an "all-ids" for every one
;; of the expressions in the (<identifier> <subst-expr>) pairings.
;; The subst-list is a ( {(<identifier> <subst-expr>)}* ) kind of list!


(define all-ids-all-exprs
  (lambda (subst-list)
    (letrec
        ((all-ids-all-exprs-r
         (lambda (sl accum-ids)
           (cond
             ((null? sl) accum-ids)
             (else
              (let*
                  ((first-id (caar sl))
                   (first-expr (cadar sl))
                   (first-ids (all-ids first-expr)) )
                (all-ids-all-exprs-r
                 (cdr sl)
                 (add-ids-to-set first-ids accum-ids) ) ) ) ) ) ))
      (all-ids-all-exprs-r subst-list '()) ) ) )

;; Need a mechanism to help us "filter-out" (via a predicate)
;; those entries in a ( {(<identifier> <subst-expr>)}* ) list
;; for which the <identifier> part shows up in a list.
;; Should use foldl operation, most likely:
(define subst-filter
  (lambda (subst-list id-list)
    (foldl
     (lambda (i a)
       (let ((sym (car i)))
         (cond
           ((memv sym id-list) a)
           (else (cons i a) ) ) ) )
     '()
     subst-list
     )
    )
  )

;; Find the corresponding <subst-expr> in the given
;;   ( {(identifier> <subst-expr>)}* )
;; given the identifier in question:
(define find-subst
  (lambda (id subst-list)
    (cond
      ((null? subst-list) '())
      (else
       (let ((first-id (caar subst-list))
             (first-expr (cadar subst-list)) )
         (cond
           ((equal? first-id id) first-expr)
           (else (find-subst id (cdr subst-list)))) ) ) ) ) )

;; (define subst-1 (cons (list 'a (parse-lambda-expr '(f x))) (list (list 'y (parse-lambda-expr '(lambda (n) (n f))))) ) )
;; (equal? (all-ids-all-exprs subst-1) '(n f n x f))

(define lambda-calc-multi-subst
  (lambda (exp         ;; The expression which must be changed.
           subst-list) ;; This is a ( { ( <identifier> <subst-expr> ) }* )
    ;; i.e., this is supposed to calculate 
    ;;   exp[subst-exp/subst-id]
    ;; AND avoid variable capture!
    (let
        ;; Seems to me that we need to know what
        ;; the ids are inside subst-exp
        ;; so that we can check to see if any
        ;; bound id's we find in exp are
        ;; a match for an id in the subst-exp?
        ( (se-ids (all-ids-all-exprs subst-list)) )
      (letrec
          ((subst
            (lambda (exp)
              (cases
               lambda-expr exp
               (const-expr (eks) exp)
               (id-expr
                (id)
                (cond ((equal? id subst-id) subst-exp)
                      (else exp)))
               (lambda-abst
                (arg-list body)
                ;; iset is the set-of-id's-which are in
                ;; both the arg-list and the subst-expr.
                ;;
                (cond
                  ;; If the subst-id is in the arg-list,
                  ;; then it's a bound var in exp
                  ;; and no substitution is allowed or needed.
                  ((memv subst-id arg-list) exp)
                  ;; If there are identifiers in common between
                  ;; the arg-list and the
                  ;; identifiers used in the subst-expr,
                  ;; then we must rename the common identifier
                  ;; instances inside the arg-list and the body
                  ;; of the exp (which is a lambda-abst)
                  ;; and the substitution must be performed
                  ;; on the new version of the lambda-abst.
                  (else
                   (let
                       ((iset (id-list-intersection arg-list se-ids) ))
                     (cond
                       ((not (null? iset))
                        (let*
                            ((fresh-list (fresh-ids body iset))
                             (new-lambda-abst
                              (lambda-abst
                               (replace-ids arg-list fresh-list)
                               (lambda-subst-helper3 body fresh-list) ) ) )
                          (subst new-lambda-abst) ) )
                       ;; If there weren't any identifiers in
                       ;; common between the arg-list
                       ;; and the identifiers used in the subst-expr,
                       ;; then all that is necessary is to
                       ;; calculate the substitution on the
                       ;; lambda-abst's body.
                       ((null? iset)
                        (lambda-abst arg-list (subst body)) ) ) ) ) ) )
                (if-expr
                 (test-expr true-expr false-expr)
                 (if-expr (subst test-expr) (subst true-expr) (subst false-expr)))
                (appl-expr
                 (rator rands)
                 (appl-expr
                  (subst rator)
                  (expr-list-subst subst rands)))
                (else (eopl:error 'lambda-calculus-subst
                                  "Invalid abstract syntax ~s" exp) ) ) ) ) )
           (subst exp) ) ) ) )



;; *****************************************************

;; Usage:  (lambda-subst-helper <exp> <list-of-substs>)
;; where <exp> is a lambda-calculus expression
;;     <list-of-substs> ::=
;;         ( )
;;       | ( (<old-var> <new-expr>) . <list-of-substs> )
;; and the idea is that each of the (<old-var> <new-expr>)
;; "pairs" must be
;; used to recursively calculate:
;;   (lambda-calculus-subst <exp> (cdar <list-of-substs>) (caar <list-of-substs>))
;; This recursively applies a sequence of substitutions
;; to an expression, one at a time.
;;
;; THERE IS A POTENTIAL PROBLEM HERE, FOR WHAT HAPPENS IF TWO
;; DIFFERENT SUBSTITUTIONS, IN GENERAL, AFFECT EACH OTHER?
;; FOR EXAMPLE, IF THERE ARE TWO SUBSTITUTIONS, THEN THIS DOES:
;;   (expr[e1/x1])[e2/x2]
;; BUT WE NEED TO BE SURE THAT THIS IS WHAT WE WANT, FOR WHAT IF
;; [e1/x1] INTRODUCES FREE VARIABLE INSTANCES OF x2, WHICH IS
;; TOUCHED BY THE SECOND SUBSTITUTION?  IF THAT HAPPENS TO BE
;; THE CASE, THEN ALL OCCURRENCES OF x2 IN (expr[e1/x1]) WILL
;; BE REPLACED WITH e2.
;;
;; WHEN THE SEQUENCE OF SUBSTITUTIONS IS DONE TO MAP FROM
;; ONE VARIABLE TO A "FRESH" VERSION OF ITSELF, THEN THIS
;; DOES WHAT WE WANT.  OTHERWISE, THIS MAY NOT DO
;; WHAT WE INTEND.
(define lambda-subst-helper
  (lambda (exp list-of-substs)
    (cond ((null? list-of-substs) exp)
          (else (lambda-subst-helper
                 (lambda-calculus-subst exp (id-expr (cadar list-of-substs)) (caar list-of-substs))
                 (cdr list-of-substs)) ) ) ) )

(define lambda-subst-helper2
  (lambda (exp list-of-substs)
    (cond ((null? list-of-substs) exp)
          (else (lambda-subst-helper2
                 (lambda-calculus-subst2 exp (id-expr (cadar list-of-substs)) (caar list-of-substs))
                 (cdr list-of-substs)) ) ) ) )

(define lambda-subst-helper3
  (lambda (exp list-of-substs)
    (cond ((null? list-of-substs) exp)
          (else (lambda-subst-helper3
                 (lambda-calculus-subst3 exp (id-expr (cadar list-of-substs)) (caar list-of-substs))
                 (cdr list-of-substs)) ) ) ) )

(define expr-list-subst
  (lambda (subst-fn rands)
    (map subst-fn rands)))

(define replace-ids
  (lambda (ids fresh-list)
    (map (lambda (i) (subst-from-list i fresh-list)) ids)))

;; This might be useful later, to execute a substitution
;; later:  looks up the corresponding new symbol from a list
;; of lists of (old-symbol, new-symbol) pairings produced
;; by the fresh-ids function.
(define subst-from-list
  (lambda (i sil)
    (cond
     ((null? sil) i)
     ((equal? i (caar sil)) (cadar sil))
     (else (subst-from-list i (cdr sil) ) ) ) ) )

;; so, fpred might be:  (lambda (elt) (cond ((subst-from-list elt my-pairs) #f) (else #t)))
;; where the my-pairs is a list of substitution-pairs.  The point is to see if there's
;; an entry in the list-of-pairs to match the elt, because we'll use it to discard
;; elements, eh?
(define filter-list
  (lambda (l fpred dl)
    (cond
     ((null? l) dl)
     ((fpred (car l)) (filter-list (cdr l) fpred (cons (car l) dl)) )
     (else (filter-list (cdr l) fpred dl) ) ) ) )

;; A tool to calculate the set of symbols which appear
;; in both the idl AND the sym-set.  Uses the straightforward,
;; naive techniques for now.
;; If an item from idl appears at least once in sym-set, then
;; it will appear in the resulting set, calculated as iset.
(define id-list-intersection-r
  (lambda (idl sym-set iset)
    (cond ((null? idl) iset)
          ((memv (car idl) sym-set)
           (id-list-intersection-r (cdr idl) sym-set (cons (car idl) iset)))
          (else (id-list-intersection-r (cdr idl) sym-set iset)) ) ) )

(define id-list-intersection
  (lambda (idl sym-set)
    (id-list-intersection-r idl sym-set '())))


;; "Unit tests!"
(define le-expr (parse-lambda-expr '(lambda (p) (f p z))))
(unparse-lambda-expr (lambda-calculus-subst le-expr (parse-lambda-expr '((lambda (z) (m z)) p) ) 'f))

(define le1 (parse-lambda-expr '(lambda (y) (f (lambda (f) (f y)) g))))
(unparse-lambda-expr (lambda-calculus-subst le1 (parse-lambda-expr '(lambda (y) (g y))) 'f))

(define le4 (parse-lambda-expr '(lambda (y) (f (lambda (f) (f g)) g))))
(unparse-lambda-expr (lambda-calculus-subst le4 (parse-lambda-expr '(lambda (y) (g y))) 'f))
(unparse-lambda-expr (lambda-calculus-subst2 le4 (parse-lambda-expr '(lambda (y) (g y))) 'f))
(unparse-lambda-expr (lambda-calculus-subst3 le4 (parse-lambda-expr '(lambda (y) (g y))) 'f))

(unparse-lambda-expr (lambda-calculus-subst3 le4 (parse-lambda-expr '(lambda (z) (w z))) 'f) )

(define le5 (parse-lambda-expr '(lambda (y z) (f z (lambda (p) (p z)) (m n)))))
(unparse-lambda-expr le5)
(unparse-lambda-expr (parse-lambda-expr '(twelve eks)))
(unparse-lambda-expr (lambda-calculus-subst le5 (parse-lambda-expr '(twelve eks)) 'z))
(unparse-lambda-expr (lambda-calculus-subst3 le5 (parse-lambda-expr '(twelve eks)) 'z))
(unparse-lambda-expr (lambda-calculus-subst3 le5 (parse-lambda-expr '(twelve eks)) 'm))