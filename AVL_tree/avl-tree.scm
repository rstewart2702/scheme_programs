;; This is a Scheme implementation of AVL search trees.
;; By default, this is a kind of persistent data structure,
;; because of the way in which Scheme list structures operate.
;;
;; The other thing this tries to do is see how far we can push
;; the "represent everything as a Lisp list" paradigm.
;;

;; Proposed AVL tree grammar, in the spirit of the wonderful book,
;;   Essentials of Programming Languages
;; by Wand and Friedman.
;;
;; <tree> ::= ()
;;          | ( <node> <tree> <tree> )
;;
;; <node> ::= ( <datum> <height> )
;;
;; <avl-tree> ::= ( <comp-fcn> <tree> )
;;


(define make-trec
  (lambda (k h) (list k h)) )

(define is-empty?
  (lambda (tree)
    (null? tree) ))

; These are "notational convenience" functions, to ease the definition
; of the tree-manipulation functions.  I suppose these should be macros?
; Also:  We assume that there is indeed a cadr or a caddr available,
; i.e., the tree must not be empty.  This can be verified via the
; is-empty? function.

; Pluck out the left child-tree:
(define lchild
  (lambda (ts) (cadr ts)) )
; Pluck out the right child-tree:
(define rchild
  (lambda (ts) (caddr ts)) )

; Pluck out the key from a tree:
(define tkey
  (lambda (ts) (car (trec ts))))
; Accessor function to retrieve the "key-and-height"
; pair from the internal structure of the tree:
(define trec
  (lambda (ts) (car ts)))

; Accessor function to retrieve the
; user-supplied comparison function so that
; the tree-derivation functions may use it:
(define comparer
  (lambda (ts) (car ts)) )

; Unpack the tree-structure from its container:
(define get-tree
  (lambda (tc) (cadr tc)) )

; Pluck out the height stored within the "car" of
; the tree structure:
(define theight
  (lambda (ts)
    (cond
      ((is-empty? ts) -1) ;; two alternatives:  an empty tree either has height 0 or -1...
                          ;; the choice affects how "full" the resulting tree shall be.
      (else (cadr (trec ts)))) ) )

;
;; INTERNAL "CONSTRUCTION HELPER-FUNCTIONS," MAINLY FOR INTERNAL AND
;; DIAGNOSTIC USE:
; Create an empty node with the given key:
(define mknode
  (lambda (k) (list (make-trec k 0) '() '() ) ) )
; Build up a tree-node from available key-structure,
; left-tree, and right-tree:
(define mktree
  (lambda (v lt rt) (list v lt rt)))
;

(define tree-shell
  (lambda (comp-fcn node)
    (list comp-fcn node) ) )

; Derive a new "tree root" that must reference the
; comparison function the user provides.
;
; The comparison function must accept two key values
; from data structures provided by the user, extracted
; from the tree structure within the balance-tree
; functions:
(define new-tree
  (lambda (k comp-fcn)
    (tree-shell comp-fcn (mknode k)) ) )


; compare keys of two different trees rooted at x and y:
;; (define kcomp
;;   (lambda (x y) (< (tkey x) (tkey y))))
;; (define kcomp
;;   (lambda (x y) (< x y)))

;; At present, we can store strings into an avl-tree
;; if we define kcomp to use the string<? function
;; instead of <, which is used to compare numbers:
;; (define kcomp
;;   (lambda (x y) (string<? (tkey x) (tkey y))))
;; Here's a nice set of string-tests:
;; (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (remove-from-tree (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (b-insert (mknode "Gaddis, C") "Stewart, R") "Selle, B") "Franklin, R") "Lin, Z") "Richardson, K") "McClinton, R") "Skaarsgard, A") "Skaarsgard, S") "Khan, Shah Rukh") "Horton, G") "Desmond, C") "Johnson, H") "DeHaviland, O") "Ford M") "Goyer, D") "Nolan, C") "Boyens, P") "Chartier, D") "Carton, S") "Khan, Shah Rukh") "Khan, SR") "Rai, A") "Bacchan, A") "Bacchan, B") "Chopra, P") "Smith, HK") "Schwartz, L") "Tifton, P") "Teegan, R") "Sorkin, A") "Eurton, J") "Fuller, J") "Blackstone, H") "Blaauw, G") "Dijkstra, EW") "VanDerMeer, G") "Martin, C") "Lipton, J") "Paltrow, G") "Pitt, B") "Jones, TP") "Jackson, A") "Washington, G") "Madison, J") "Adams, J") "Smith, A") "Hayek, FA") "Keynes, JM") "Adams, JQ") "Buchanan, J") "Bowers, R") "Boyer, D") "Hoover, H") "Simpson, H") "Zogby, G") "Akhtar, Z") "Akhtar, F") "Leach, N") "Brasswell, R") "Barna, G") "Meyer, B") "Dybvig, RK") "Friedman, D") "Wand, M") "MacQueen, D") "Peyton-Jones, S") "Brooks, F") "Darnay, C") "Holmes, S") "Watson, J") "Calvin, J") "Wirth, N") "Gries, D") "Poythress, V")

;; This is a "generic binary tree height calculating function"
;; which recursive computes the height of a tree by traversing
;; its structure.
;;
;; It is different from the theight function, which is designed to
;; reach in a fetch the value stored in the "height field" of an
;; AVL-balanced tree.
;; Also, this function is based on a slightly different definition
;; of height from that which we used in our height-balanced AVL
;; trees:  our AVL trees define an empty tree's height as -1, not 0.
;; This was just to make some other things work out more conveniently
;; in the AVL tree functions when deriving new AVL trees and calculating
;; their height based on the heights of subtrees (some of which can be
;; empty, right?)
(define t-height
  (lambda (ts) 
    (let
        ((lc (lchild ts))
         (rc (rchild ts)))
      (cond 
        ((and (null? lc) (null? rc)) 0)   
        ((null? lc) (+ 1 (t-height rc)) ) ; when both subtrees are empty, the height is 0
        ((null? rc) (+ 1 (t-height lc)) ) ; when only the right child is empty, the height is 1 + height-of-left-child
        (else (max (+ 1 (t-height lc)) (+ 1 (t-height rc)))) ) ; this is the fully-general case, take the larger of the two heights
      ) ) )


;; Lingering issues:
;; How in the world are we to deal with an insert operation which results 
;; in empty/null subtrees?  How are we to try and make the resulting tree
;; balanced again?

;; This is the "naive" insert into a binary tree:
;; With the latest tweaks to the data structure, this won't work
;; properly without further changes!
(define t-insert
  (lambda (ts itm)
    (let
        ((newtree (mknode itm))
         (kcomp   (comparer ts)) )
      (cond 
       ((null? ts)
        ;; If we're inserting into an "empty tree" then the result is
        ;; merely the result of creating a new tree/node from the itm.
        newtree)
       ((kcomp (tkey ts) (tkey newtree)) 
        (let* ( (lc (lchild ts))
                (rc (rchild ts))
                (rt-new (t-insert rc itm)) ) ;; derive the new right-hand subtree
          (mktree 
           (make-trec (tkey ts) (+ 1 (max (theight lc) (theight rt-new)) ) )
           lc
           rt-new) ) )
       ((kcomp (tkey newtree) (tkey ts))
        (let* ( (lc (lchild ts))
                (rc (rchild ts))
                (lt-new (t-insert lc itm)) ) ;; derive the new left-hand subtree
          (mktree
           (make-trec (tkey ts) (+ 1 (max (theight lt-new) (theight rc)) ) )
           lt-new
           rc) ) ) ) ) ) )

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
     ((is-empty? ts) ts) ;; Corner-case of an empty tree, right?
     (else           ;; We assume that there are two non-null children, right?
      (let*
          ;; Calculate some particular items from the tree rooted at ts:
          ((rc       (rchild ts))
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
             lc-of-rc ) )
           ;; new right-hand child, new-rc
           (new-rc rc-of-rc) )
        (mktree
         (make-trec
          (tkey rc)
          (+ 1 (max (theight new-lc) (theight new-rc))) )
          new-lc
          new-rc ) ) ) ) ) )

(define r-rotate
  (lambda (ts)
    (cond
     ((is-empty? ts) ts) ;; Corner-case of an empty tree, right?
     (else
      (let*
          ((rc       (rchild ts))
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
             ) ) )
        (mktree
         (make-trec
          (tkey lc)
          (+ 1 (max (theight new-lc) (theight new-rc)) ) )
         new-lc
         new-rc ) ) ) ) ) )

(define b-inorder
  (lambda (ts)
     (cond
      ((is-empty? ts) '())
      (else
       (append
        (b-inorder (lchild ts))
        (cons (tkey ts) '())
        (b-inorder (rchild ts)) ) ) ) ) )

(define b-inorder-a
  (lambda (ts)
    (letrec
        ((inorder-i
          (lambda (ts)
            (cond
             ((is-empty? ts) idf)
             (else
              (f-compose
               (f-compose
                (inorder-i (lchild ts))
                (lambda (h) (cons (tkey ts) h)))
               (inorder-i (rchild ts)) ) ) ) ) ) )
      ((inorder-i ts) '()) ) ) )
                
;; This version seems to be cheaper than b-inorder-a.
;; This version avoids adding instances of the
;; identity function (named "idf" herein) to the
;; resulting function.  Thus the resulting
;; lambda-expression is cheaper to execute.
;;
;; It's probably cheaper also because of the little
;; bit of "looking ahead" done by the nullity testing
;; of the left and right subtrees.
;;
;; Based on gross run-time testing, using a tree filled
;; with 500,000 integers, this version is a little faster
;; than even the inorder traversal which uses append.
;; And I never expected the append-based version to be
;; particularly cheap:  it was indeed quick-and-dirty.
(define b-inorder-b
  (lambda (ts)
    (letrec
        ((inorder-i
          (lambda (ts)
            (let*
                ((root-func (lambda (h) (cons (tkey ts) h)))
                 (first-func
                  (cond ((is-empty? (lchild ts)) root-func)
                        (else (f-compose (inorder-i (lchild ts)) root-func) ))) )
              (cond ((is-empty? (rchild ts)) first-func)
                    (else (f-compose first-func (inorder-i (rchild ts))) ) ) ) ) ) )
      ((inorder-i ts) '()) ) ) )

(define max-path
  (lambda (ts)
    (cond
     ((null? ts) -1) ;; important to that an empty tree has path-length -1?
     (else
      (max (+ 1 (max-path (lchild ts))) (+ 1 (max-path (rchild ts)) ) ) ) ) ) ) 

(define bt-test
  (lambda (n)
    (letrec
        ((ts (new-tree 0 <))
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
        ((ts (new-tree (- n 1) <) )
         (bt-test-tr
          (lambda (tree key limit)
            (cond
             ((equal? key limit) tree)
             (else
              (bt-test-tr (b-insert tree key) (- key 1) limit) ) ) ) )
         )
      (bt-test-tr ts (- n 2) 0) ) ) )

(define bt-test-range
  (lambda (x y)
    (letrec
        ((ts (new-tree x <))
         (bt-test-range-tr
          (lambda (tree x y)
            (cond
             ((equal? x y) (b-insert tree x))
             (else
              (bt-test-range-tr (b-insert tree x) (+ x 1) y) ) ) ) ) )
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
    (let*
        ((lc        (lchild ts))
         (rc        (rchild ts))
         (lc-height (theight lc) )
         (rc-height (theight rc) ) )
      (cond
       ((> (abs (- lc-height rc-height)) 1 )
        ;; (printf "Rebalancing needed, at key:  ~v~n" (tkey ts))
        ;; (printf "Current height:  ~v~n" (theight ts))
        ;; (printf "left child height: ~v~n" (theight (lchild ts)))
        ;; (printf "right child height: ~v~n" (theight (rchild ts)))
        (cond
         ((< lc-height rc-height)
          (let*
              ((lc-of-rc (lchild (rchild ts)))
               (rc-of-rc (rchild (rchild ts)))
               (result-tree
                (l-rotate
                 (cond
                  ((<= (theight lc-of-rc) (theight rc-of-rc))
                   ts )
                  ((> (theight lc-of-rc) (theight rc-of-rc))
                   (let
                       ( (new-rc (r-rotate rc)) )
                     (mktree
                      (make-trec
                       (tkey ts)
                       (+ 1 (max lc-height (theight new-rc))) )
                      lc
                      new-rc ) )) ) ) ) )
            ;; (printf "Rebalanced to height: ~v~n" (theight result-tree))
            result-tree ) )
         ((> lc-height rc-height)
          (let*
              ((lc-of-lc (lchild (lchild ts)))
               (rc-of-lc (rchild (lchild ts)))
               (result-tree
                (r-rotate
                 (cond
                  ((<= (theight rc-of-lc) (theight lc-of-lc))
                   ts )
                  ((> (theight rc-of-lc) (theight lc-of-lc))
                   (let
                       ( (new-lc (l-rotate lc)) )
                     (mktree
                      (make-trec
                       (tkey ts)
                       (+ 1 (max (theight new-lc) rc-height)) )
                      new-lc
                      rc ) ) ) ) ) ) )
            ;; (printf "Rebalanced to height: ~v~n" (theight result-tree))
            result-tree ) ) ) )
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
;; function which uses the above rebalance function and eliminates
;; lots of redundant definitions.

;; Using the letrec to bind newtree to (mknode itm)
;; in a context outside the recursive definition of the insertion
;; (named b-ins-inner) helps avoid unnecessary cons-ing that
;; was done in earlier version of this function.
(define b-insert
  (lambda (ts itm)
    (letrec
        ((newtree (mknode itm))
         (kcomp   (comparer ts))
         (b-ins-inner
          (lambda (ti)
            (cond 
             ((is-empty? ti)
              ;; If we're inserting into an "empty tree" then the result is
              ;; merely the result of creating a new tree/node from the itm.
              newtree)
             (else
              (let*
                  ( (lc (lchild ti))
                    (rc (rchild ti))
                    (lt-new (cond ((kcomp (tkey newtree) (tkey ti)) (b-ins-inner lc))
                                  (else lc) ) )
                    (rt-new (cond ((kcomp (tkey ti) (tkey newtree)) (b-ins-inner rc))
                                  (else rc) ) ) )
                ;; (printf "b-insert now at key ~v~n" (tkey ti))
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ti)
                   (+ 1 (max (theight lt-new) (theight rt-new))) )
                  lt-new
                  rt-new ) ) ) ) ) ) ) )
      ;; (printf "adding key ~v~n" itm)
      (tree-shell kcomp (b-ins-inner (get-tree ts)) ) ) ) )

; I started the following version of the insert operator because
; I was starting to understand that it will not always be necessary
; to invoke the rebalance function on a resulting tree, whenever
; the insert was done in a tree for which the two subtrees were
; of equal height, or when the insert was into the shorter of
; the two subtrees of an unbalanced tree.  But it seems to me that,
; in order to determine whether or not a rebalance will be needed
; after inserting into the taller side of an unbalanced tree,
; the heights of the child subtrees of the taller side must also
; be examined, right?  And I fail to see how that is much cheaper
; than simply comparing the heights of the two subtrees which
; must be reassembled back together into the resulting tree, and
; rebalancing that tree when necessary.  Maybe in an imperative
; setting, it's cheaper to do the lookahead and avoid the rebalancing,
; but the cost of storing and checking the "balance factor's" in
; order to make a "rebalancing determination" possible does not
; seem to be any cheaper than "rebalancing the resulting new
; tree, if necessary, after inserting into the subtree."
;
; If the tree is unbalanced, and we're inserting into the taller of
; the subtrees, then rebalancing could be needed?
;
; IN THE CONTEXT OF AN INSERT OPERATION:
; All of the above ruminations were due to my fundamental misunderstanding
; of the nature of rebalancing.  It turns out that the most important
; thing is that rebalancing can only decrease the height of a tree, i.e.,
; if a tree increases in height because one of its subtrees has grown
; in height by 1, then rebalancing will shrink the height of the tree
; by 1.  This means that once a rebalancing operation has been performed,
; the rotated/rebalanced tree's height has not been changed, which means
; that more rotations are not necessary.
;
; Even an imperative solution is not going to be doing "lookahead."
; Instead, a flag value is passed back from a recursive call to indicate
; that a rotation has already been performed, and that further rotations
; are not necessary.  We could do this in a Scheme solution if the
; insertion function was designed in a tail-recursive manner, and used
; an explicit stack to manage the tree traversal, so that a separate,
; tail-recursive, "use-the-stack-to-walk-back-up-to-the-root" function
; could use a "we've already done a rotation/rebalancing, so you don't
; even need to check" flag...
;

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

(define internal-remove-from-tree
  (lambda (ts k kcomp)
    (letrec
        ((rft-inner
          (lambda (ti)
            (cond
             ((kcomp k (tkey ti))
              (let
                  ((new-lc (rft-inner (lchild ti))))
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ti)
                   (+ 1 (max (theight new-lc) (theight (rchild ti)))) )
                  new-lc
                  (rchild ti) ) ) ) )
             ((kcomp (tkey ti) k)
              (let
                  ((new-rc (rft-inner (rchild ti))))
                (rebalance
                 (mktree
                  (make-trec
                   (tkey ti)
                   (+ 1 (max (theight (lchild ti)) (theight new-rc))) )
                  (lchild ti)
                  new-rc) ) ) )
             (else
              ;; The key in question, k, is in the root of tree ti.
              (cond
               ((and (is-empty? (rchild ti)) (is-empty? (lchild ti))) '() )
               (else
                (let*
                    ;; Special case needed when there is not
                    ;; a right-hand subtree from which to retrieve
                    ;; a replacement for the key to be deleted.
                    ;; When that happens, then new key comes from the left
                    ;; subtree, which can only be a leaf.
                    ((new-key
                      (cond
                       ((is-empty? (rchild ti)) (tkey (lchild ti)) )
                       (else (find-min (rchild ti)) ) ) )
                     (new-rc
                      (cond
                       ((is-empty? (rchild ti)) '() )
                       (else (internal-remove-from-tree (rchild ti) new-key kcomp)) ) )
                     (new-lc
                      (cond
                       ((is-empty? (rchild ti)) '())
                       (else (lchild ti)) ) ) )
                  (rebalance
                   (mktree
                    (make-trec
                     new-key
                     (+ 1 (max (theight new-lc) (theight new-rc))) )
                    new-lc
                    new-rc ) ) ) ) ) ) ) ) ) )
      (rft-inner ts) ) ) )
     
(define remove-from-tree
  (lambda (tc k)
    (tree-shell
     (comparer tc)
     (internal-remove-from-tree (get-tree tc) k (comparer tc)) ) ) )


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

;; Concatenation operations:
; These are used by the splitting function.
; The idea is to traverse down the left or right "spine"
; of the taller search tree, and when we arrive at a
; subtree which is as tall or shorter than the shorter
; subtree, we construct a new subtree which has the
; provided key as its root, and then that result is
; incorporated back into the overall tree, rebalancing
; as necessary, rather like an insert had occurred.
(define lconcat-key
  ;; The left-hand tree is considered to be the taller one in this case.
  ;;
  ;; Here's a more "operational/imperative" interpretation:
  ;; This function recursively calculates a new left-hand tree
  ;; from the right-child of the existing left-hand tree, in order to
  ;; reduce the height of the left-hand tree, until we recursively reach
  ;; a left-hand tree which has the correct height.  Then, the two are
  ;; spliced together, with the split-key at the root, and that spliced
  ;; result is rebalanced.  This result is returned to the caller, which
  ;; derives a new tree from the left and right trees, with the key from
  ;; the root of the left-hand tree as the key that falls between the
  ;; returned right-hand tree, and the existing left-hand tree.  In other
  ;; words, this recursively derives a new right-hand tree by travelling
  ;; down the right-hand spine of the left-hand tree, stopping when
  ;; the height of the right-hand subtree is "small enough, but not too
  ;; small!"
  ;;
  ;; Base Case:
  ;; Both trees satisfy is-empty? predicate, so the only thing to do
  ;; is create a new tree with the split-key as the root.
  ;; When both trees satisfy the is-empty? predicate, they have equal
  ;; height as well.  The result will be the derivation of a tree of
  ;; height 0 with empty left and right subtrees.
  ;;
  ;; N.B. this is not explicit in the code.  It just happens
  ;; to be a consequence of the height tests performed by the code!
  ;;
  ;; Also, the two trees may be non-empty, but equal in height,
  ;; or they only differ in height by 1 (which is also implicit
  ;; in this situation...)  In this case, a balanced tree can be
  ;; built of the left tree, the split-key, and the right tree.
  ;;
  ;; Induction:
  ;; The left tree is taller than the right tree, so we need a new
  ;; right-hand tree (called new-tr) by (recursively) calculating:
  ;;   (lconcat-key (rchild tl) tr split-key)
  ;; and the new left-hand tree (named new-tl) is:  (lchild tl)
  ;; and the new key (named new-key) is:  (tkey tl).
  ;;
  ;; The recursive use of lconcat-key calculates the concatenation
  ;; of a shorter left-hand tree (i.e., (rchild tl)) to the right-hand
  ;; tree, named tr.  (The recursion is supposed to reduce the height
  ;; differences between the two trees.)
  ;;
  ;; Calculating the rebalanced version of the tree is necessary
  ;; because the tree calculated by the recursive call to lconcat-key
  ;; can differ in height from (lchild tl) by more than 1.
  ;;
  ;; (Will rebalancing be necessary?  Strictly speaking, probably only
  ;; once, as is (probably) the case with insertion of a new key.)
  (lambda (tl tr split-key)
    (let*
        ((height-eq (equal? (theight tl) (theight tr)) )
         (height-gt (<      (theight tl) (theight tr)) ) ; right-hand tree is taller?
         (new-key (cond ((or height-gt height-eq) split-key)
                        (else (tkey tl)) ) )
         (new-tr  (cond ((or height-gt height-eq) tr)
                        (else (lconcat-key (rchild tl) tr split-key) ) ) )
         (new-tl  (cond ((or height-gt height-eq) tl)
                        (else (lchild tl))) ) )
      (rebalance
       (mktree
        (make-trec
         new-key
         (+ 1 (max (theight new-tl) (theight new-tr))) )
        new-tl
        new-tr ) ) ) ) )
;
; [2013-04-15 Mon]
; Rebalancing needed only when the resulting tree grows in height by 1,
; AND the resulting height throws the parent off-balance by 1, i.e., the
; two siblings differ in height by 2.
; I need to understand whether or not these operations ever need to
; calculate the rebalance'd version of the new subtree, i.e., whether
; or not those rebalance operations are ever needed.
; [2013-04-29 Mon] see the commentary inside the lconcat-key function
; for some tentative conclusions about the necessity of rebalancing,
; and the inductive arguments for the correctness of the concatenation
; operations.
;
; Some "facts" about concatentation of a shorter right-hand tree onto a
; taller left-hand tree:
; + In the process of traversing down the right spine of the left-hand
;   tree, we may come to a place in which the left-hand tree is shorter
;   than the right-hand tree.  It must be the case that "when this happens,"
;   the left-hand tree must be 1 shorter than the right-hand tree.  Why?
;   If we started out with AVL trees, then the "right spine" of the left
;   tree must be a tree that is at least 1 taller than the right-hand
;   tree.  This means that the right-child of that right spine tree
;   could be the same height as the right tree, or one shorter.
; 
(define rconcat-key
  (lambda (tl tr split-key)
    (let*
        ((height-eq (equal? (theight tl) (theight tr)) )
         (height-gt (>      (theight tl) (theight tr)) )
         (new-key (cond ((or height-gt height-eq) split-key)
                        (else (tkey tr)) ) )
         (new-tr  (cond ((or height-gt height-eq) tr)
                        (else (rchild tr)) ) )
         (new-tl  (cond ((or height-gt height-eq) tl)
                        (else (rconcat-key tl (lchild tr) split-key)))) )
      (rebalance
       (mktree
        (make-trec
         new-key
         (+ 1 (max (theight new-tl) (theight new-tr))) )
        new-tl
        new-tr ) ) ) ) )

;; lconcat and rconcat concatenate trees together and
;; are defined in terms of the lconcat-key and rconcat-key.
;; The idea is to derive the "splitting key" from the right-hand
;; tree in the concatenation.
(define lconcat
  (lambda (tl tr)
    (let
        ((new-key (find-min tr)) )
      (lconcat-key tl (remove-from-tree tr new-key) new-key) ) ) )

(define rconcat
  (lambda (tl tr)
    (let
        ((new-key (find-min tr)) )
      (rconcat-key tl (remove-from-tree tr new-key) new-key) ) ) )


;; Splits a balanced tree t, by key value skey, so that
;; all keys < skey are in (car (b-split t skey))
;; and all keys > skey are in (cdr (bsplit t skey))
;;
;; It's amazing how quickly this falls into place when
;; one finally understands how to leverage the well-ordering
;; properties of the tree structure, and how the
;; root node stranded by the splitting of a subtree can become
;; the root node when deriving a concatenation, which is how
;; those rconcat-key and lconcat-key functions are used.

(define b-split-curriable
  (lambda (kcomp)
    (letrec
        ((b-split-i
          (lambda (t kn)
            (cond
              ((is-empty? t) (list '() '() '()))
              ((equal? (tkey t) kn)
               (list (lchild t) (rchild t) kn) )
              ;; If the key falls to the left of the current root,
              ;; then split the left subtree by the key, and
              ;; concatenate together the right-hand side of the
              ;; current root, the right-hand side of the split left
              ;; subtree, and the splitting key.  This becomes
              ;; the right-hand side of the split, and the left-hand
              ;; side of the split is the left-hand tree that resulted
              ;; from the split of the left-hand subtree.
              ((kcomp kn (tkey t))
               (let ((sr (b-split-i (lchild t) kn) ) )
                 (list
                  (ptn-left-tree sr)
                  (rconcat-key (ptn-right-tree sr) (rchild t) (tkey t))
                  (ptn-key sr) ) ) )
              ;; If the key falls to the right of the current root,
              ;; then split the right subtree by the key, and
              ;; concatenate together the left-hand side of the
              ;; current root, the left-hand side of the split right
              ;; subtree, and the splitting key.  This becomes
              ;; the left-hand side of the split, and the right-hand
              ;; side of the split is the right-hand tree that resulted
              ;; from the split of the right-hand subtree.
              ((kcomp (tkey t) kn)
               (let ( (sr (b-split-i (rchild t) kn) ) )
                 (list
                  (lconcat-key (lchild t) (ptn-right-tree sr) (tkey t) )
                  (ptn-right-tree sr)
                  (ptn-key sr) ) ) ) ) ) ) )
      b-split-i) ) )

;; Utilities to retrieve the various parts of the result
;; of a partitioning or "splitting."
;; Assumption is that the three components will become the
;; three elements of an ordinary list, for now:
(define ptn-left-tree
  (lambda (presult)
    (car presult)))
(define ptn-right-tree
  (lambda (presult)
    (cadr presult)) )
(define ptn-key
  (lambda (presult)
    (caddr presult)))

(define b-split
  (lambda (t skey)
    (letrec
        ((kcomp (comparer t))
         (b-split-i (b-split-curriable kcomp) ) )
      (let
          ( (result (b-split-i (get-tree t) skey)) )
        (list
         (tree-shell (comparer t) (car result))
         (tree-shell (comparer t) (cdr result)) ) ) )) )

;; This is a range-search operation:
;; it may not be particularly efficient,
;; partly because of the use of append, and
;; partly because of the intrinsic nature of the
;; height-balanced tree structure.
;;
(define f-compose
  (lambda (f g) (lambda (h) (f (g h)))) )
(define idf
  (lambda (x) x))

;; I don't yet have a good feel for whether or not
;; this can decay into something akin to a linear
;; list scan, but a moment's reflection seems to
;; imply that it's possible that the well-ordering
;; of the tree means that big chunks of the key-space
;; can be eliminated during the search for items which
;; fall into the range specified by x and y.
;;
;; This version of the range-retrieval function uses
;; "list-construction-as-function-composition" to help
;; guarantee that we won't need another linear pass
;; through an assembled list, and won't need the
;; append function to add to the list.  But overall,
;; so many implementations of append are so darn fast,
;; it's hard to see the difference, at least when the
;; keys are integers.  So, the trade-off is possibly
;; an even one, for many Scheme implementations?  Still,
;; the append function can get expensive, and its cost
;; may be easier to notice on a different machine or
;; implementation?
(define b-list-range-a
  (lambda (t x y)
    (letrec
        ((kcomp (comparer t))
         (lr-inner
          (lambda (ti)
            (cond
             ((is-empty? ti) idf)
             (else
              (let
                  ((left-res
                    (cond
                     ((and (not (is-empty? (lchild ti)))
                           (or (kcomp x (tkey ti))
                               (kcomp y (tkey ti))))
                      (lr-inner (lchild ti)))
                     (else idf) ) )
                   (mid-res
                    (cond
                     ((and (or (kcomp x (tkey ti)) (equal? (tkey ti) x))
                           (or (kcomp (tkey ti) y) (equal? (tkey ti) y)))
                      (lambda (h) (cons (tkey ti) h)))
                     (else idf) ) )
                   (right-res
                    (cond
                     ((and (not (is-empty? (rchild ti)))
                           (or (kcomp (tkey ti) x)
                               (kcomp (tkey ti) y)))
                      (lr-inner (rchild ti)) )
                     (else idf) ) ) )
                (f-compose (f-compose left-res mid-res) right-res) ) ) ) ) ) )
      ((lr-inner (get-tree t)) '()) ) ) )

;; Newer "cursor" functions:
;; Trying to create a "cursor" which can be used to traverse the collection
;; the avl-tree represents.
;;
;; This calls for some more abstractions than are here presently, because
;; these ridiculous calls to cadar, etc, help to make a simple idea
;; absolutely impenetrable.  This needs to be addressed.
;;
;; Plus, it'd be nice if these could somehow be expressed as "folds" or something,
;; since it seems reasonable to expect to be able to apply a function to each
;; item retrieved via these "cursor" structures.
;;
;; More than anything else, I was just trying to understand what a "zipper" is
;; as well, and what "zippers" seem to do is similar to what I am trying to
;; do here (except a traversal via one of these cursors is unidirectional,
;; whereas generalized zippers are supposed to let you do bidirectional
;; traversals.

; Builds up a "forest" of trees by walking down the "left spine"
; of the given avl tree, in this case.
(define walk-down-left
  (lambda
      (ct    ; "current tree"...?
       frst) ; "forest" of trees...?
    (cond
     ((is-empty? ct) frst)
     ((is-empty? (lchild ct))
      (cons (list (trec ct) (rchild ct)) frst))
     (else
      (walk-down-left
       (lchild ct)
       (cons (list (trec ct) (rchild ct)) frst)) ) ) ) )

(define cursor-desc
  (lambda (tree)
    (let
        ((start-forest
          (list (list (trec tree) (rchild tree) ) ) ) )
      (walk-down-left (lchild tree) start-forest) ) ) )

(define cursor-next
  (lambda
      (frst)
    (cond
     ((null? frst) '())
     (else
      (walk-down-left
       (cadar frst)
       (cdr frst) ) ) ) ) )

(define b-cur-inorder
  (lambda
      (tree)
    (letrec
        ((trav
          (lambda (cur lst)
            (cond
             ((null? cur) lst)
             (else
              (trav (cursor-next cur)
                    (cons (caaar cur) lst)) ) ) ) ) )
      (trav (cursor-desc tree) '()) ) ) )



;; (define cursor-next
;;   (lambda
;;       (frst)
;;     (cond
;;      ((null? frst) '())
;;      (else
;;       (cons
;;        (cdar frst)
;;        (walk-down-left
;;         (cdar frst)
;;         (cddr frst) ) ) ) ) ) )

    ;; (cond
    ;;  ((null? frst) '())
    ;;  ((null? (cadar frst))
    ;;   (cons
    ;;    ; (caadr frst)
    ;;    (cadr frst)
    ;;    (walk-down-left
    ;;      (cadadr frst)
    ;;      (cddr frst) ) )) ) ) )

;; (cond
;;  ((null? (lchild (caar cur)))
;;   (build-up
;;    (cons (process-func (tkey (caar cur))) res-list)
;;    (advance-cursor-to-next)
;;    )
;;   )
;;  (else
;;   () ) )

;; (define b-asc-cursor
;;   (lambda (t kt)
;;     (letrec
;;         ((kcomp (comparer t))
;;          (ba-inner
;;           (lambda (left-accum right-remain)
;;             (cond
;;              ((null? (
      

;; This version of b-list-range tries to avoid the
;; use of the identity function as much as possible
;; by "looking ahead," just as was done with the
;; b-inorder-b function.  But rough benchmarking
;; in guile does not show a performance edge over the
;; b-list-range-a function, which is in turn much
;; faster than the list-range-1 function, which is
;; the naive "list-retrieval-by-consing-and-reversing."
(define b-list-range-b
  (lambda (t x y)
    (letrec
        ((kcomp (comparer t))
         (lr-inner
          (lambda (ti)
            (cond
             ((is-empty? ti) idf)
             (else
              (let*
                  ((left-res
                    (cond
                     ((and (not (is-empty? (lchild ti)))
                           (or (kcomp x (tkey ti))
                               (kcomp y (tkey ti))))
                      (lr-inner (lchild ti)))
                     (else '()) ) )
                   (mid-res
                    (cond
                     ((and (or (kcomp x (tkey ti)) (equal? (tkey ti) x))
                           (or (kcomp (tkey ti) y) (equal? (tkey ti) y)))
                      (lambda (h) (cons (tkey ti) h)))
                     (else '()) ) )
                   (right-res
                    (cond
                     ((and (not (is-empty? (rchild ti)))
                           (or (kcomp (tkey ti) x)
                               (kcomp (tkey ti) y)))
                      (lr-inner (rchild ti)) )
                     (else '()) ) )
                   (first-func
                    (cond ((and (null? left-res) (null? mid-res)) '())
                          ((null? left-res) right-res)
                          ((null? right-res) mid-res)
                          (else (f-compose left-res mid-res)) ) ) )
                (cond
                 ((and (null? first-func) (null? right-res)) idf)
                 ((null? first-func) right-res)
                 ((null? right-res)  first-func)
                 (else (f-compose first-func right-res)) ) ) ) ) ) ) )
      ((lr-inner (get-tree t)) '()) ) ) )

;; Same as b-list-range-a, but uses the following functions
;; provided in the guile implementation:
;;   compose
;;   identity
;; Their meaning should be obvious...
(define b-list-range-b
  (lambda (t x y)
    (letrec
        ((kcomp (comparer t))
         (lr-inner
          (lambda (ti)
            (cond
             ((is-empty? ti) idf)
             (else
              (let
                  ((left-res
                    (cond
                     ((and (not (is-empty? (lchild ti)))
                           (or (kcomp x (tkey ti))
                               (kcomp y (tkey ti))))
                      (lr-inner (lchild ti)))
                     (else identity) ) )
                   (mid-res
                    (cond
                     ((and (or (kcomp x (tkey ti)) (equal? (tkey ti) x))
                           (or (kcomp (tkey ti) y) (equal? (tkey ti) y)))
                      (lambda (h) (cons (tkey ti) h)))
                     (else identity) ) )
                   (right-res
                    (cond
                     ((and (not (is-empty? (rchild ti)))
                           (or (kcomp (tkey ti) x)
                               (kcomp (tkey ti) y)))
                      (lr-inner (rchild ti)) )
                     (else identity) ) ) )
                (compose (compose left-res mid-res) right-res) ) ) ) ) ) )
      ((lr-inner (get-tree t)) '()) ) ) )

(define b-list-range
  (lambda (t x y)
    (letrec
        ((kcomp (comparer t))
         (lr-inner
          (lambda (ti)
            (cond
             ((is-empty? ti) '())
             (else
              (append
               (cond
                ((and (not (is-empty? (lchild ti)))
                      (or (kcomp x (tkey ti))
                          (kcomp y (tkey ti)) ) )
                 (lr-inner (lchild ti)) )
                (else '()) )
               (cond
                ((and (or (kcomp x (tkey ti)) (equal? (tkey ti) x))
                      (or (kcomp (tkey ti) y) (equal? (tkey ti) y)))
                 (cons (tkey ti) '()) )
                (else '()) )
               (cond
                ((and (not (is-empty? (rchild ti)))
                      (or  (kcomp (tkey ti) x)
                           (kcomp (tkey ti) y)) )
                 (lr-inner (rchild ti)) )
                (else '()) ) ) ) ) ) ) )
      (lr-inner (get-tree t)) ) ) )

;; The simple operations:
(define b-find
  (lambda (tc x)
    (letrec
        ((ti (get-tree tc))
         (kcomp (comparer tc))
         (b-find-i
          (lambda (t)
            (cond
             ((is-empty? t) '())
             ((kcomp (tkey t) x) (b-find-i (rchild t) ))
             ((kcomp x (tkey t)) (b-find-i (lchild t) ))
             (else (tkey t)) ) ) ) )
      (b-find-i ti) ) ) )

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

(define list-range
  (lambda (lst x y)
    (cond
     ((null? lst) '())
     ((and (<= x (car lst)) (<= (car lst) y))
      (cons (car lst) (list-range (cdr lst) x y)))
     (else (list-range (cdr lst) x y)) ) ) )

(define list-range-1
  (lambda (lst x y)
    (letrec
        ((lr-tr
          (lambda (lst x y lr)
            (cond
             ((null? lst) lr)
             ((and (<= x (car lst)) (<= (car lst) y))
              (lr-tr (cdr lst) x y (cons (car lst) lr)) )
             (else (lr-tr (cdr lst) x y lr) ) ) ) ) )
      (reverse (lr-tr lst x y '())) ) ) )

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

;;
(define strs-tree-2 (new-tree "Stewart, Richard" string<?))
(define strs-tree-1 (list string<? ()))



;; New "set-union" function defined in terms of concatenation.
;; We shall have to change the b-split function to retrieve the
;; sought-after element, if it is present in the tree-set being
;; partitioned, so that b-split will provide some indication of
;; whether or not the sought-after element was actually present
;; in the set being partitioned or "split."
;;
;; Also, b-split must change to take into account the possibility
;; that the sought-after element or datum does not appear in the
;; tree-set.
;;
;(define set-union
;  (lambda (tl tr)
;    (let*
;	((int-tl (get-tree tl))
;	 (int-tr (get-tree tr))
;	 (kcomp (comparer tl)) )
;      (
(define set-union
  (lambda (tl tr)
    (let*
        ((kcomp         (comparer tl))
         (int-tl        (get-tree tl))
         (int-tr        (get-tree tr))
         ;; this derives a partitioning function for us!
         (set-partition (b-split-curriable kcomp)) )
      (letrec
          ((set-union-i
            (lambda (tleft tright)
              (cond
                ((is-empty? tleft) tright)
                ((is-empty? tright) tleft)
                (else ; both tree-sets are non-empty?
                 (let*
                     ((trpk (tkey tright))
                      (presult (set-partition tleft trpk))
                      (pl (ptn-left-tree presult))
                      (pr (ptn-right-tree presult))
                      (ul (set-union-i pl (lchild tright)))
                      (ur (set-union-i pr (rchild tright))) )
                   ;; the ul and ur are non-overlapping sets, yes?  So they must be concatenated back together, right?
                   (cond
                     ((<= (theight ul) (theight ur)) (rconcat-key ul ur trpk) )
                     ((<  (theight ur) (theight ul)) (lconcat-key ul ur trpk) ) ) ) ) ) ) ) )
        (set-union-i int-tl int-tr) ) ) ) ) 

(define set-intersection
  (lambda (tl tr)
    (let*
        ((kcomp     (comparer tl))
         (int-tl    (get-tree tl))
         (int-tr    (get-tree tr))
         (set-partition (b-split-curriable kcomp)) )
      (letrec
          ((set-intersection-i
            (lambda (tleft tright)
              (cond
                ; Intersection of empty set with anything is the empty set!
                ((is-empty? tleft) '())
                ((is-empty? tright) '())
                ; Otherwise, must deal with case of both sets not empty:
                (else
                 (let*
                     ((trpk (tkey tright))
                      (presult (set-partition tleft trpk))
                      (pl (ptn-left-tree presult))
                      (pr (ptn-right-tree presult))
                      (pk (ptn-key presult))
                      (il (set-intersection-i pl (lchild tright)) )
                      (ir (set-intersection-i pr (rchild tright)) ) )
                   ;; The il and ir must be concatenated back together:
                   (display il)(display "\n")(display ir)(display "\n\n")
                   (cond
                     ((not (null? pk))
                      (cond
                        ((<= (theight il) (theight ir)) (lconcat-key il ir pk))
                        ((<  (theight il) (theight ir)) (rconcat-key il ir pk)) ) )
                     ;;
                     (else ;; The "partitioning key" was not present in the partitioned set:
                      (cond
                       ((and (not (is-empty? il)) (not (is-empty? ir)) )
                        (cond
                          ((<= (theight il) (theight ir))
                           (let ((sk (find-min ir)))
                             (lconcat-key il (remove-from-tree ir sk) sk)) )
                          ((<  (theight il) (theight ir))
                           (let ((sk (find-min ir)))
                             (rconcat-key il (remove-from-tree ir sk) sk)) ) ) )
                       ((is-empty? il) ir)
                       ((is-empty? ir) il)
                       (else (display "SHOULDN'T HAPPEN!\n") ) ) ) ) ) ) ) ) ) )
        (set-intersection-i int-tl int-tr)) ) ) )


;(cond
;        ((is-empty? tl) int-tr)
;        ((is-empty? tr) int-tl)
;        ;;
;        (else ; both sets are non-empty?
;         (let*
;             ((pk            (tkey int-tr))
;              (presult       (set-partition tl pk))
;              (pl            (car presult))
;              (pr            (cadr presult))
;              (ul            (set-union pl (lchild pr)))
;              (ur            (set-union pr (rchild pr
;

