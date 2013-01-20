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
                      ;; the choice affects how "full" the resulting tree shall be.
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

;; N.B. There are lots of places in the following code in which the
;; difference between heights-of-subtrees is very important.
;; As I was working these functions out, it turns out that the
;; calculation of the differences between tree heights shows up
;; everywhere.  For example, in the tree-rotation functions l-rotate
;; and r-rotate, this is codified in the conditional expressions
;; which calculate the height of a new subtree by checking to see
;; whether or not both of the proposed new children of this new
;; subtree are empty, in which case the height of the new subtree
;; shall be 0, and otherwise, the usual calculation,
;;   (+ 1 (max height-of-left height-of-right))
;; is performed, where "height-of-left" and "height-of-right"
;; have already been calculated.
;;
;; After writing the initial version of the code, I have come to
;; understand that when one considers the height of an empty
;; tree (a tree ts for which ((lambda (x) (null? x)) ts) returns #t)
;; to be -1, then the height-difference calculations "work out
;; properly," and we don't need the crufty conditional expression
;; which is all over the place, in slightly different forms, etc.
;; It's yucky, repetitious code which should be eliminated, etc.
;; 

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
           ;; new left-hand child, new-lc, is:
           (new-lc 
            (mktree
             ;; root of new-lc is the key from the existing tree...
             (make-trec
              (tkey ts)
              (+ 1 (max lc-height lc-of-rc-height)) )
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
          (+ 1 (max (theight new-lc) (theight new-rc))) )
          new-lc
          new-rc ) ) ) ) ) )

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
           ;; new right-hand child, new-rc, is:
           (new-rc
            (mktree
             ;; root of new-rc is the key from the existing tree...
             (make-trec
              (tkey ts)
              (+ 1 (max rc-height rc-of-lc-height)) )
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
          (+ 1 (max (theight new-lc) (theight new-rc)) ) )
         new-lc
         new-rc ) ) ) ) ) )


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
                       (+ 1 (max (theight lc) (theight rt-new))) )
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
                         (+ 1 (max (theight lc) (theight new-rc)) ) )
                        lc
                        new-rc ) ) ) ) ) )
                 (else
                  ;; no adjustments were needed, just return the kind of tree we always would have:
                  (mktree
                   (make-trec
                    (tkey ts)
                    (+ 1 (max (theight lc) (theight rt-new)) ) )
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
                       (+ 1 (max (theight lt-new) (theight rc)) ) )
                      lt-new
                      rc ) ) )
                   ((kcomp lt-new newtree)
                    (let
                        ( (new-lc (l-rotate lt-new)) )
                      (r-rotate
                       (mktree
                        (make-trec
                         (tkey ts)
                         (+ 1 (max (theight new-lc) (theight rc)) ) )
                        new-lc
                        rc ) ) ) ) ) )
                 (else
                  (mktree
                   (make-trec
                    (tkey ts)
                    (+ 1 (max (theight lt-new) (theight rc)) ) )
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

;; We need a helper function which traverses a tree to find the
;; smallest key in it, and then deletes it.  This would seem to be
;; a matter of taking every leftward link possible until you run out,
;; and then

(define find-min
  (lambda (ts)
    (cond
     ((null? (lchild ts)) (tkey ts))
     (else (find-min (lchild ts)) ) ) ) )

;; This is intended to calculate the tree with the smallest key
;; removed:
;;
;; We must separate concerns:  This should *only* "recurse" down
;; to the minimal node, and then get rid of it.  And after that
;; happens, the returned tree should be rebalanced, right, and the
;; rebalancing operations must propagate all the way back up to
;; the root...
;;
;; A remove-min is the result of recalculating all of the left-most
;; subtrees, isn't it?
(define remove-min
  (lambda (ts)
      (cond
       ((null? (lchild ts))
        ;; This is the "base-case.":
        ;; The left subtree is empty, and therefore this is the node to be excised.
        ;; This subtree must be replaced by its sibling from the right-hand
        ;; side:
        (rchild ts) )
       (else
         ;; This is the "recursive-case":
         ;; We must re-derive the resulting tree, rooted at ts, and
         ;; derived the properly balanced version, at that.
         (letrec
             (;; We need the new right-hand subtree?
              ;; We need the new left-hand subtree (obtained by the recursive
              ;; call to remove-min, yes?)
              ;; We may need to do an l-rotate on the right-hand subtree, if
              ;; its left-child is "too tall," i.e., the right-hand subtree
              ;; is left-heavy.
              (new-lchild (remove-min (lchild ts)))
              (rc-height (theight (rchild ts)) ) )
           (cond
            ((> (abs (- ((theight new-lchild) (rc-height)))) 1)
             ;; If the two subtrees' heights differ by more than 1,
             ;; then some rebalancing of the search tree is necessary.
             (letrec
                 ((rc (rchild ts))
                  (lc-of-rc (lchild rc))
                  (rc-of-rc (rchild rc))
                  (lc-of-rc-height (theight lc-of-rc))
                  (rc-of-rc-height (theight rc-of-rc)) )
             (cond
              ((> (lc-of-rc-height) (rc-of-rc-height))
               ;; If the right-hand side of the present subtree is
               ;; "left-heavy," then it should be r-rotate'd so that
               ;; the final l-rotate'd tree will come out at the
               ;; correct height.
               (let
                   ((new-rc (r-rotate rc)) )
                 (l-rotate
                  (mktree
                   (make-trec
                    (tkey ts)
                    (+ 1 (max (theight new-lchild) (theight new-rc)) ) )
                   new-lchild
                   new-rc ) ) ) )
              (else
               ;; The right-hand side of the present subtree is not
               ;; "left-heavy" so the rebalanced tree is simply the
               ;; l-rotate of the present subtree.
               (l-rotate
                (mktree
                 (make-trec
                  (tkey ts)
                  (+ 1 (max (theight new-lchild) (theight rc))) )
                 new-lchild
                 rc) ) ) ) ) )
            (else
             (mktree
              (make-trec
               (tkey ts)
               (+ 1 (max (theight new-lchild) (theight rc) ) ) )
              new-lchild
              rc) ) ) ) ) ) ) )

(define rebalance
  (lambda (ts)
     (letrec
         ((lc        (lchild ts))
          (rc        (rchild ts))
          (lc-height (theight lc) )
          (rc-height (theight rc) ) )
       (cond
        ((> (abs (- lc-height rc-height)) 1 )
         (cond
          ((< lc-height rc-height)
           (let
               ((lc-of-rc (lchild (rchild ts)))
                (rc-of-rc (rchild (rchild ts))) )
             (cond
              ((> (theight lc-of-rc) (theight rc-of-rc))
               (let
                   ((new-rc (r-rotate rc)) )
                 (l-rotate
                  (mktree
                   (make-trec
                    (tkey ts)
                    (+ 1 (max lc-height (theight new-rc))))
                   lc
                   new-rc) ) ) )
              ((<= (theight lc-of-rc) (theight rc-of-rc))
               (l-rotate ts) ) ) ) )
          ((> lc-height rc-height)
           (let
               ((lc-of-lc (lchild (lchild ts)))
                (rc-of-lc (rchild (lchild ts))) )
             (cond
              ((> (theight rc-of-lc) (theight lc-of-lc))
               (let
                   ((new-lc (l-rotate lc)) )
                 (r-rotate
                  (mktree
                   (make-trec
                    (tkey ts)
                    (+ 1 (max (theight new-lc) rc-height)) )
                   new-lc
                   rc ) ) ) )
              ((<= (theight rc-of-lc) (theight lc-of-lc))
               (r-rotate ts) ) ) ) ) ) )
        (else ts) ) ) ) )

;; So, a deletion function must:
;; calculate the root of the subtree which contains the key to
;; be deleted, and:
;; + Calculate the successor key (via a find-min calculation)
;; + Calculate a new right-hand subtree with the successor's key
;;   removed (via remove-min call)
;; + calculate a new, balanced subtree by:
;;   making the calculated successor the new subtree root,
;;   making the existing left-subtree as the left-subtree,
;;   making the right-hand-subtree calculated above the right-subtree
;;
;; this new subtree shall have to be balanced...

;; I now realize that the above will have to be generalized into a
;; "remove-this-key" function, I think.  Then, the delete-an-item
;; function shall have to:
;; + find the key-to-be-removed,
;; + find the successor of the key-to-be-removed (via find-min)
;; + calculate the new right-hand subtree, with the
;;   successor removed (via the "remove-this-key" function)
;; + calculate the new tree:
;;   with the successor key as the root,
;;   the present left tree as the left subtree,
;;   the calculated new right-hand subtree as the right subtree
;;   This new tree may need an r-rotate of the right-hand subtree,
;;   and may need to be l-rotated itself?

(define remove-from-tree
  (lambda (ts k)
    (let
        ( (kt (mknode k)) )
      (cond
       ((null? (lchild ts))
        (rchild ts) )
       ((kcomp kt ts)
        (let
            ((new-lc (remove-from-tree (lchild ts) k)))
          (rebalance
           (mktree
            (make-trec
             (tkey ts)
             (+ 1 (max (theight new-lc) (theight (rchild ts)))) )
            new-lc
            (rchild ts) ) ) ) )
       ((kcomp ts kt)
        (let
            ((new-rc (remove-from-tree (rchild ts) k)))
          (rebalance
           (mktree
            (make-trec
             (tkey ts)
             (+ 1 (max (theight (lchild ts)) (theight new-rc))) )
            (lchild ts)
            new-rc ) ) ) )
       (else
        ;; The key in question, k, is in the root of the tree ts.
        (let
            ((new-key (find-min ts))
             (new-rc (remove-from-tree (rchild ts) k)) )
          (rebalance
           (mktree
            (make-trec
             new-key
             (min (+ 1 (max (theight (lchild ts)) (theight new-rc))) ) )
            (lchild ts)
            new-rc) ) ) ) ) ) ) )