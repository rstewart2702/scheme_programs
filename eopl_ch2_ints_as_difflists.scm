;; Exercise 2.3
;; This was all about representing integers via "difference lists."
;; In this kind of data structure, an integer is represented as a 
;; pair of lists stored in a Lisp list tagged with the symbol diff.
;; Here's the grammar:
;;   DiffTree ::= (one) | (diff DiffTree DiffTree)
;; The value of the integer is thus equal to the value of the first
;; tree minus the value of the second, i.e., every integer is represented
;; as a pair of trees, X and Y, and its value is (X-Y).
;;
;; A key insight into this is the "indirectness" of the representation.
;; One increments by subtracting -1, which *seems indirect* when working
;; with ordinary integers, and which *is direct* when working with
;; this alternative representation.

;; The exercises were:
;Exercise 2.3 [**] Define a representation of all the integers (negative and nonnegative) as diff-trees, where
;a diff-tree is a list defined by the grammar
;
;  Diff-tree ::= (one) | (diff Diff-tree Diff-tree)
;
;The list (one) represents 1. If t1 represents n1 and t2 represents n2,
;then (diff t1 t2) is a representation of n1 – n2.
;
;So both (one) and (diff (one) (diff (one) (one))) are representations of 1; 
;(diff (diff (one) (one)) (one)) is a representation of –1.
;
; 1.  Show that every number has infinitely many representations in this system.
;
; 2.  Turn this representation of the integers into an implementation by writing zero, is-zero?, successor, and predecessor,
;     as specified on page 32, except that now the negative integers are also represented. Your procedures should take as input
;     any of the multiple legal representations of an integer in this scheme. For example, if your successor procedure is given
;     any of the infinitely many legal representations of 1, it should produce one of the legal representations of 2. It is
;     permissible for different legal representations of 1 to yield different legal representations of 2.
;
; 3.  Write a procedure diff-tree-plus that does addition in this representation. Your procedure should be optimized for the
;     diff-tree representation, and should do its work in a constant amount of time (independent of the size of its inputs).
;     In particular, it should not be recursive.


;; show-difftree traverses a difflist structure and subtracts the
;; result of evaluating the righthand side from the result of 
;; evaluating the lefthand side.
;;
;; show-difftree :: DiffTree -> Int
(define show-difftree
  (lambda (tree)
    (cond 
      [ (eqv? (car tree) 'one) 1 ]
      [ (eqv? (car tree) 'diff) 
        (letrec 
            [ (lhstree (cadr tree) )
              (rhstree (caddr tree) ) 
              (lresult (show-difftree lhstree) )
              (rresult (show-difftree rhstree) ) ]
          (display (list lresult rresult))
          (display "\n")
          (display tree) (display "\n\n")
          (- lresult rresult) ) ] ) ) )

(define zero (list 'diff (list 'one)(list 'one)))

;; Successor function:
;; successor :: DiffTree -> DiffTree
(define successor
  (lambda (tree)
    ;; Derive a new number by subtracting -1 from it!
    (list 'diff tree (list 'diff zero '(one)))
    ;; This alternative implementation derives a new integer
    ;; by adding 1 to the negation of the old integer, i.e.,
    ;; by deriving the pair (1, (0-x)), which is 
    ;;   1 - (0-x) == 1 - (-x) == 1 + x
    ;; (list 'diff '(one) (list 'diff zero tree))
    ))

;; Predecessor function
;; predecessor :: DiffTree -> DiffTree
(define predecessor
  (lambda (tree)
    (list 'diff tree '(one))))

;; The idea I had for the "add" function was as follows:  
;; diff-tree-plus :: DiffTree -> DiffTree -> DiffTree
(define diff-tree-plus
  [lambda (ltree rtree)
    ;; Pair the left operand with the negation of the right operand.
    ;; This "adds" the numbers together in constant time, regardless
    ;; of the size of the structures.
    [list 'diff ltree (list 'diff zero rtree)]
    ;; If we had a cheap way to determine whether or not the 
    ;; right-hand tree of the left operand was equal to the left-hand
    ;; tree of the right operand, then we could simply splice 
    ;; together the left tree of the left operand and the right tree
    ;; of the right operand.  Vide:
    ;;   (x-y)+(y-z) == x-y+y-z == x-z,
    ;; when x,y,z are all integers.
    ;; But I don't think it's quite that simple, and we can't universally
    ;; apply such an optimization, even though that would likely simplify
    ;; the resulting structures!
    ] )

;(define huh?
;  (list 'diff (list 'diff (list 'one) (list 'diff (list 'one) zero)) zero))
;
;(define two-1
;  (list 'diff (list 'diff (list 'diff (list 'one) zero) zero) zero) ) 
;
;(show-difftree
; '(diff (diff (diff (diff (one) (diff (one)(one))) (diff (one)(one))) (diff (one)(one)) ) (diff (one)(one))) )
;
;(show-difftree
; '(diff (one) (diff (diff (one)(one)) (diff (diff (one)(one)) (diff (diff (one)(one)) (one))) ) ) )
;
;(show-difftree
; '(diff (diff (one)(one)) (diff (one) (diff (one) (diff (one)(one)))))  )
;
;(show-difftree
; '(diff (one) (diff (one) (diff (one)(one))) ) )
;
;(show-difftree '(diff (one) (diff (diff(one)(one)) (one))))
;
;(define my-two
;  '(diff (one) (diff (diff(one)(one)) (one))))

(define four (successor (successor ( successor '(one)) ) ) )
(define two (successor '(one)))
;; The following structure results from (diff-tree-plus two four):
;(diff
; (diff (one) (diff (diff (one) (one)) (one)))
; (diff
;  (diff (one) (one))
;  (diff (diff (diff (one) (diff (diff (one) (one)) (one))) (diff (diff (one) (one)) (one))) (diff (diff (one) (one)) (one)))))
