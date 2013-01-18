(define trec
  (lambda (ts) (car ts)))
(define make-trec
  (lambda (k h) (list k h)) )

; These are "notational convenience" functions, to ease the definition
; of the tree-manipulation functions.  I suppose these should be macros?
; Pluck out the left child-tree:
(define lchild
  (lambda (ts) (cadr ts)))
; Pluck out the right child-tree:
(define rchild
  (lambda (ts) (caddr ts)))
; Pluck out the key from a tree:
(define tkey
  (lambda (ts) (car (trec ts))))
; Pluck out the height stored within the "car" of
; the tree structure:
(define theight
  (lambda (ts)
    (cond
     ((null? ts) -1)  ;; two alternatives:  an empty tree either has height 0 or -1...
                      ;; the choice may affect how "full" the resulting tree shall be
     (else (cadr (trec ts)))) ) )

;
; Create an empty node with the given key:
(define mknode
  (lambda (k) (list (list k 0) '() '() )) )
; Build up a tree:
(define mktree
  (lambda (v lt rt) (list v lt rt)))
;
; compare keys of two different trees rooted at x and y:
(define kcomp
  (lambda (x y) (< (tkey x) (tkey y))))

(define t-height
  (lambda (ts) 
    (let ((lc (lchild ts))
          (rc (rchild ts)))
      (cond 
        ((and (null? lc) (null? rc)) 0) ; when both subtrees are empty, the height is 0
        ((null? lc) (+ 1 (t-height rc)) ) ; when only the left child is empty, the height is 1 + height-of-right-child
        ((null? rc) (+ 1 (t-height lc)) ) ; when only the right child is empty, the height is 1 + height-of-left-child
        (#t (max (+ 1 (t-height lc)) (+ 1 (t-height rc)))) ; this is the fully-general case, take the larger of the two heights
        ) 
      ) 
    ) 
  )

;; Lingering issues:
;; How in the world are we to deal with an insert operation which results 
;; in empty/null subtrees?  How are we to try and make the resulting tree
;; balanced again?

;; This is the "naive" insert into a binary tree:
(define t-insert
  (lambda (ts itm)
    (let ((newtree (mknode itm))
          )
      (cond 
         ((null? ts)
          ;; If we're inserting into an "empty tree" then the result is
          ;; merely the result of creating a new tree/node from the itm.
          newtree)
         ((kcomp ts newtree) 
          (letrec ( (lc (lchild ts))
                    (rc (rchild ts))
                    (rt-new (t-insert rc itm)) ;; derive the new right-hand subtree
                    )
            (mktree 
             (make-trec (tkey ts) (+ 1 (max (theight lc) (theight rt-new)) ) )
             lc
             rt-new) ) )
         ((kcomp newtree ts)
          (letrec ( (lc (lchild ts))
                    (rc (rchild ts))
                    (lt-new (t-insert lc itm)) ;; derive the new left-hand subtree
                    )
            (mktree
             (make-trec (tkey ts) (+ 1 (max (theight lt-new) (theight rc)) ) )
             lt-new
             rc) ) )
         )
      )
    )
  )

;; If we're to l-rotate a binary tree, then it must already possess two
;; children, correct?
(define l-rotate
  (lambda (ts)
    (cond
     ((null? ts) ts) ;; Corner-case of an empty tree, right?
     (else           ;; We assume that there are two non-null children, right?
      (letrec
          (
           ;; Calculate some particular items from the tree rooted at ts:
           (rc       (rchild ts))
           (lc       (lchild ts))
           (lc-of-rc (lchild rc))
           (rc-of-rc (rchild rc))
           (lc-height (theight lc))
           (lc-of-rc-height (theight lc-of-rc))
           ;;; (rc-of-rc-height (theight rc-of-rc))
           ;;
           ;; Calculation of new subtrees:
           ;;
           (new-height
            (cond
             ((and (null? lc) (null? lc-of-rc)) 0 )
             (else (+ 1 (max lc-height lc-of-rc-height))) ) )
           ;; new left-hand child, new-lc, is:
           (new-lc 
            (mktree
             ;; root of new-lc is the key from the existing tree...
             (make-trec (tkey ts) new-height)
             ;; and its left subtree is the lc (left-hand child) of original tree...
             lc
             ;; and its right subtree is the lc-of-rc
             lc-of-rc
             )
            )
           ;; new right-hand child, new-rc
           (new-rc
            rc-of-rc)
           )
        (mktree
         (make-trec
          (tkey rc)
          (cond
           ((and (null? new-lc) (null? new-rc)) 0)
           (else (+ 1 (max (theight new-lc) (theight new-rc))) )) )
          new-lc
          new-rc
          )
         )
        )
      )
     )
    )

(define r-rotate
  (lambda (ts)
    (cond
     ((null? ts) ts) ;; Corner-case of an empty tree, right?
     (else
      (letrec
          (
           (rc       (rchild ts))
           (lc       (lchild ts))
           (lc-of-lc (lchild lc))
           (rc-of-lc (rchild lc))
           (rc-height (theight rc))
           ;;; (lc-of-lc-height (theight lc-of-lc))
           (rc-of-lc-height (theight rc-of-lc))
           ;;
           ;; Calculation of new subtrees:
           ;;
           ;; new left-hand child, new-lc
           (new-lc
            lc-of-lc)
           ;;
           (new-height
            (cond
             ((and (null? rc) (null? rc-of-lc)) 0 )
             (else (+ 1 (max rc-height rc-of-lc-height)) ) ) )
           ;; new right-hand child, new-rc, is:
           (new-rc
            (mktree
             ;; root of new-rc is the key from the existing tree...
             (make-trec (tkey ts) new-height)
             ;; and the left-subtree is the right-hand child of the left subtree, lc...
             rc-of-lc
             ;; and the right-subtree is the right-hand child of existing tree
             rc
             )
            )
           )
        (mktree
         (make-trec
          (tkey lc)
          (cond
           ((and (null? new-lc) (null? new-rc)) 0)
           (else (+ 1 (max (theight new-lc) (theight new-rc)))) ) )
         new-lc
         new-rc
         )
        )
      )
     )
    )
  )


;; This is the insert-with-balancing into a height-balanced binary tree:
;; It's puzzling to me that inserting a bunch of keys in sequential order
;; results in a tree with lots of single-child nodes down at the leaf
;; level:  so many of the leaves don't have siblings!  What's up with that?
;; I think it may be a consequence of the ordering of the keys, and the fact
;; that it's not like b*tree, in which there's a distinction between the
;; data-nodes and internal nodes.  So, is's much less of an approximation
;; of a complete binary tree than I thought...

(define b-insert
  (lambda (ts itm)
    (let ((newtree (mknode itm)) )
      (cond 
         ((null? ts)
          ;; If we're inserting into an "empty tree" then the result is
          ;; merely the result of creating a new tree/node from the itm.
          newtree)
         (else
          (let
              ( (lc (lchild ts))
                (rc (rchild ts)) )
            (cond
             ((kcomp ts newtree)
              (let ( (rt-new (b-insert rc itm)) )
                (cond
                 ((> (abs (- (theight rt-new) (theight lc)) ) 1)
                  ;; If one subtree's too much taller than the other, then we must adjust the resulting
                  ;; search tree:
                  (cond
                   ((kcomp rt-new newtree) ;; new key is greater than root of new, right-hand sub-tree...
                    (l-rotate
                     (mktree
                      (make-trec
                       (tkey ts)
                       (cond
                        ((and (null? lc) (null? rt-new)) 0 )
                        (else (+ 1 (max (theight lc) (theight rt-new))) ) ) )
                      lc
                      rt-new ) ) )
                   ;;
                   ((kcomp newtree rt-new)
                    (let
                        ( (new-rc (r-rotate rt-new)) ) ;; The r-rotate'd new rhs sub-tree is is required...
                      ;; to derive the l-rotate'd final result.
                      (l-rotate
                       (mktree
                        (make-trec
                         (tkey ts)
                         (cond
                          ((and (null? lc) (null? new-rc)) 0)
                          (else (+ 1 (max (theight lc) (theight new-rc)) ) ) ) )
                        lc
                        new-rc ) ) ) ) ) )
                 (else
                  ;; no adjustments were needed, just return the kind of tree we always would have:
                  (mktree
                   (make-trec
                    (tkey ts)
                    (cond
                     ((and (null? lc) (null? rt-new)) 0 )
                     (else (+ 1 (max (theight lc) (theight rt-new)) ) ) ) )
                   lc
                   rt-new) ) ) ) )
             ((kcomp newtree ts)
              (let ( (lt-new (b-insert lc itm)) )
                (cond
                 ((> (abs (- (theight lt-new) (theight rc)) ) 1)
                  (cond
                   ((kcomp newtree lt-new)
                    (r-rotate
                     (mktree
                      (make-trec
                       (tkey ts)
                       (cond
                        ((and (null? lt-new) (null? rc)) 0 )
                        (else (+ 1 (max (theight lt-new) (theight rc)) ) ) ) )
                      lt-new
                      rc ) ) )
                   ((kcomp lt-new newtree)
                    (let
                        ( (new-lc (l-rotate lt-new)) )
                      (r-rotate
                       (mktree
                        (make-trec
                         (tkey ts)
                         (cond
                          ((and (null? new-lc) (null? rc)) 0 )
                          (else (+ 1 (max (theight new-lc) (theight rc)) ) ) ) )
                        new-lc
                        rc ) ) ) ) ) )
                 (else
                  (mktree
                   (make-trec
                    (tkey ts)
                    (cond
                     ((and (null? lt-new) (null? rc)) 0)
                     (else (+ 1 (max (theight lt-new) (theight rc)) ) ) ) )
                   lt-new
                   rc) ) ) ) ) ) ) ) ) ) ) )

(define b-inorder
  (lambda (ts)
    ;; (reverse
     (cond
      ((null? ts) '())
      (else
       (append
        (b-inorder (lchild ts))
        (cons (tkey ts) '())
        (b-inorder (rchild ts)) ) ) ) ) );;  )

(define max-path
  (lambda (ts)
    (cond
     ((null? ts) 0)
     (else
      (max (+ 1 (max-path (lchild ts))) (+ 1 (max-path (rchild ts)) ) ) ) ) ) ) 

(define bt-test
  (lambda (n)
    (letrec
        ((ts (mknode 0))
         (bt-test-tr
          (lambda (tree key limit)
            (cond
             ((equal? key limit) tree)
             (else
              (bt-test-tr (b-insert tree key) (+ 1 key) limit) ) ) ) ) )
      (bt-test-tr ts 1 n) ) ) )

(define bt-test-d
  (lambda (n)
    (letrec
        ((ts (mknode (- n 1)))
         (bt-test-tr
          (lambda (tree key limit)
            (cond
             ((equal? key limit) tree)
             (else
              (bt-test-tr (b-insert tree key) (- key 1) limit) ) ) ) )
         )
      (bt-test-tr ts (- n 2) 0) ) ) )


;; Probably need a "primitive function" which finds the successor to a 
;; given key value:  we'll need something like that in order to delete
;; things properly, right?

;; I'm continually amazed by the simplicity and intellectual horsepower
;; provided by a functional programming language.  It makes thought much
;; simpler and cleaner, helps provide the essentials of the inductive
;; reasoning, etc.

