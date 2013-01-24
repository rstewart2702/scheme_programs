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
              (bt-test-tr (b-insert2 tree key) (+ 1 key) limit) ) ) ) ) )
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
              (bt-test-tr (b-insert2 tree key) (- key 1) limit) ) ) ) )
         )
      (bt-test-tr ts (- n 2) 0) ) ) )

(define bt-test-range
  (lambda (x y)
    (letrec
        ((ts (mknode x) )
         (bt-test-range-tr
          (lambda (tree x y)
            (cond
             ((equal? x y) (b-insert2 tree x))
             (else
              (bt-test-range-tr (b-insert2 tree x) (+ x 1) y) ) ) ) ) )
      (bt-test-range-tr ts (+ x 1) y) ) ) )
         


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

;; This is the insert-with-balancing into a height-balanced binary tree:
;; It's puzzling to me that inserting a bunch of keys in sequential order
;; results in a tree with lots of single-child nodes down at the leaf
;; level:  so many of the leaves don't have siblings!  What's up with that?
;; I think it may be a consequence of the ordering of the keys, and the fact
;; that it's not like b*tree, in which there's a distinction between the
;; data-nodes and internal nodes.  So, is's much less of an approximation
;; of a complete binary tree than I thought...
;; 
;; Ah!  It turned out to be a bit of a fine point:
;; Once I changed the theight function to define the height of an empty
;; tree as -1, then there was an easy distinction between the height of
;; an empty tree and the height of a single-node tree.  This made the
;; tree-structure more "complete," and obviated some special-case
;; code.

;; The following is a rewritten version of the b-insert
;; function which usese the above rebalance function and eliminates
;; lots of redundant definitions.

(define b-insert2
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
              (let ( (rt-new (b-insert2 rc itm)) )
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ts)
                   (+ 1 (max (theight lc) (theight rt-new)) ) )
                   lc
                   rt-new) ) ) )
             ((kcomp newtree ts)
              (let ( (lt-new (b-insert2 lc itm)) )
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ts)
                   (+ 1 (max (theight lt-new) (theight rc)) ) )
                  lt-new
                  rc) ) ) ) ) ) ) ) ) ) )


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
;; + find the key-to-be-removed;
;; + find the successor of the key-to-be-removed (via find-min)
;; + calculate the new right-hand subtree, with the
;;   successor removed (via the "remove-this-key" function)
;; + calculate the new tree:
;;   with the successor key as the root,
;;   the present left tree as the left subtree,
;;   the calculated new right-hand subtree as the right subtree
;;   This new tree may need an r-rotate of the right-hand subtree,
;;   and may need to be l-rotated itself?
;;
;;   Yes, and this new tree is calculated by the rebalance function,
;;   and generalizing that functionality out into its own function
;;   made it possible to derive a very concise version of the
;;   function to calculate the result of inserting into a balanced
;;   search tree.

(define remove-from-tree
  (lambda (ts k)
    (letrec
        ((kt (mknode k))
         (rft-inner
          (lambda (ti)
            (cond
             ;; ((null? (lchild ti))
             ;;  (rchild ti) )
             ((kcomp kt ti)
              (let
                  ((new-lc (rft-inner (lchild ti) )))
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ti)
                   (+ 1 (max (theight new-lc) (theight (rchild ti)))) )
                  new-lc
                  (rchild ti) ) ) ) )
             ((kcomp ti kt)
              (let
                  ((new-rc (rft-inner (rchild ti))))
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ti)
                   (+ 1 (max (theight (lchild ti)) (theight new-rc))) )
                  (lchild ti)
                  new-rc ) ) ) )
             (else
              ;; The key in question, k, is in the root of the tree ti.
              (cond
               ((and
                 (null? (rchild ti))
                 (null? (lchild ti)) )
                '() )
               (else
                (letrec
                    ;; Special case needed when there is not
                    ;; a right-hand subtree from which to retrieve
                    ;; a replacement for the key to be deleted.
                    ;; When that happens, then new key comes from the left
                    ;; subtree, which can only be a leaf.
                    ((new-key
                      (cond
                       ((null? (rchild ti)) (tkey (lchild ti)))
                       (else (find-min (rchild ti))) ) )
                     (new-rc
                      (cond
                       ((null? (rchild ti)) '() )
                       (else (remove-from-tree (rchild ti) new-key)) ) )
                     (new-lc
                      (cond
                       ((null? (rchild ti)) '())
                       (else (lchild ti) ) ) ) )
                  (rebalance
                   (mktree
                    (make-trec
                     new-key
                     (+ 1 (max (theight new-lc) (theight new-rc))) )
                    new-lc
                    new-rc) ) ) ) ) ) ) ) ) )
      (rft-inner ts) ) ) )

(define del-test-350
  (lambda ()
    (letrec
        ((big-tree (bt-test 350))
         (remove-loop
          (lambda (n ts)
            (cond
             ((equal? n 0) ts)
             (else
              (remove-loop (- n 1) (remove-from-tree ts n)) ) ) ) ) )
      (remove-loop 120 big-tree ) ) ) ) 

;; This all needs to be factored further, and the specifications could be
;; further re-cast in such a manner that let or letrec expressions
;; should be utilized more heavily.  The reason this would be desirable
;; is because it may yield more efficient code (by reducing the redundant
;; calculation of expressions) and code which resembles mathematical
;; definitions, much like code in a Haskell program (which just goes to
;; show the common heritage anyhow, right...)

;; This concatenation operator will only work properly
;; when (>= (theight tl) (theight tr)).
;; But it is cheap and concise!
;;
;; It should not take much to generalize this into a
;; version which allows the shorter tree to be the left-hand
;; tree, and in which we "splice together" the shorter left-hand
;; tree and a "left-most" subtree of the right-hand, taller tree
;; and then splice that into the taller right-hand tree, with
;; rebalancing cascading up to the root.
;;
;; Frustrating, trying to describe this stuff in such
;; imperative, figurative terms...
;; 
(define concat
  (lambda (tl tr)
    (cond
     ((equal? (theight tl) (theight tr))
      (letrec ((new-key (find-min tr))
               (new-tr (remove-from-tree tr new-key)) )
        (rebalance
         (mktree
          (make-trec
           new-key
           (+ 1 (max (theight tl) (theight new-tr) ) ))
          tl
          new-tr) ) ) )
     (else
      (let ( (new-rc (concat (rchild tl) tr) ) )
        (rebalance
         (mktree
          (make-trec
           (tkey tl)
           (+ 1 (max (theight (lchild tl)) (theight new-rc))) )
          (lchild tl)
          new-rc ) ) ) ) ) ) )

;; This is a range-search operation:
;; it may not be particularly efficient,
;; partly because of the use of append, and
;; partly because of the intrinsic nature of the
;; height-balanced tree structure.
;;
;; I don't yet have a good feel for whether or not
;; this can decay into something akin to a linear
;; list scan, but a moment's reflection seems to
;; imply that it's possible that the well-ordering
;; of the tree means that big chunks of the key-space
;; can be eliminated during the search for items which
;; fall into the range specified by x and y.
;;
(define list-range
  (lambda (t x y)
    (letrec
        ((xnode (mknode x))
         (ynode (mknode y))
         (lr-inner
          (lambda (ti)
            (cond
             ((null? ti) '())
             (else
              (append
               (cond
                ((and (not (null? (lchild ti)))
                      (or (kcomp xnode ti)
                          (kcomp ynode ti) ) )
                 (lr-inner (lchild ti)) )
                (else '()) )
               (cond
                ((and (or (kcomp xnode ti) (equal? (tkey ti) (tkey xnode)))
                      (or (kcomp ti ynode) (equal? (tkey ti) (tkey ynode))) )
                 (cons (tkey ti) '()) )
                (else '()) )
               (cond
                ((and (not (null? (rchild ti)))
                      (or  (kcomp ti xnode )
                           (kcomp ti ynode )) )
                 (lr-inner (rchild ti)) )
                (else '()) ) ) ) ) ) ) )
      (lr-inner t) ) ) )

;; The simple operations:
(define b-find
  (lambda (ts x)
    (cond
     ((null? ts) '())
     ((kcomp ts (mknode x)) (b-find (rchild ts) x))
     ((kcomp (mknode x) ts) (b-find (lchild ts) x))
     (else (tkey ts)) ) ) )

;; SOME FUNCTIONS USEFUL FOR BUILDING "REGULAR" LISTS IN ORDER
;; TO DO COMPARISON TESTING.
;; These make it possible to perform rudimentary timing comparisons
;; so that we can demonstrate the lower costs of balanced tree
;; searching.

(define list-find
  (lambda (lst x)
    (cond
     ((null? lst) '())
     ((equal? x (car lst)) x)
     (else (list-find (cdr lst) x)) ) ) )

(define list-gen
  (lambda (n)
    (letrec
        ((list-gen-tr
          (lambda (gen-lst ni)
            (cond
             ((equal? ni 0) (cons ni gen-lst))
             (else (list-gen-tr (cons ni gen-lst) (- ni 1)) ) ) ) ) )
      (list-gen-tr (cons (- n 1) '()) (- n 2)) ) ) )

;; The huge differences start to show up once the size of the set
;; gets up to 100000, so it seems.  But those are just ad hoc tests,
;; done off the cuff, using racket's time function...

