;; This is a Scheme implementation of AVL search trees.
;; By default, this is a kind of persistent data structure,
;; because of the way in which Scheme list structures operate.
;;
;; This implementation uses the define-datatype and cases "forms"
;; to provide definitions of the data structures and nicere syntax
;; for functions which manipulate search trees.  "Underneath," 
;; everything is still a list structure, but the define-datatype
;; and cases provide a nice mechanism for examining the various
;; parts of a tree, and they provide a nice framework in which to
;; manipulate the search tree structures.
;;
;; This has turned out to be relatively easy to translate from the
;; original version of the code which did not use define-datatype and
;; cases.
;;
;; This could serve as the foundation for a relatively efficient
;; "associative lookup" data structure that is also a purely functional
;; persistent data structure.
;;
(define is-datum?
  (lambda (x) #t))

(define-datatype data-type data-type?
  (datum
   (internal-data is-datum?) ) )

(define-datatype key-type key-type?
  (key-datum
   (internal-key is-datum?)))

(define-datatype tree-set tree-set?
  (tree-set-structure
   (comparer procedure?)   ;; a function used to compare keys, e.g., < for numbers
   (tree-root search-tree?);; this is the search tree structure itself.
   ) )

;; So, I think this is the way one would define an empty tree-set?
;; (tree-set-structure string<? (empty-tree)) 

(define-datatype search-tree search-tree?
  (empty-tree)
  (search-tree-structure
   (key-part key-type?)     ;; the value of the key goes here
   (data-part data-type?)   ;; optional data part
   (height number?)
   (left-child search-tree?)
   (right-child search-tree?) ) )

(define ts-insert
  (lambda (ts key data)
    (letrec
        ((ts-ins-inner
          (lambda (root k d ord-pred?)
            (cases
             search-tree root
             (empty-tree
              ()
              (search-tree-structure k d 0 (empty-tree) (empty-tree)))
             (search-tree-structure
              (key-part data-part height left-child right-child)
              (let*
                  ((lt-new (cond ((ord-pred? k key-part)
                                  (ts-ins-inner left-child k d ord-pred?))
                                 (else left-child)) )
                   (rt-new (cond ((ord-pred? key-part k)
                                  (ts-ins-inner right-child k d ord-pred?))
                                 (else right-child) ) ) )
                (ts-rebalance
                 (search-tree-structure
                  key-part
                  data-part
                  (+ 1 (max (height-of lt-new) (height-of rt-new)))
                  lt-new
                  rt-new) ) ) ) ) ) ) )
      (cases
       tree-set ts
       (tree-set-structure
        (comparer tree-root)
          (tree-set-structure
           comparer
           (ts-ins-inner tree-root key data comparer)) ) ) ) ) )

(define tree-of
  (lambda (ts)
    (cases
     tree-set ts
     (tree-set-structure
      (comparer tree-root)
      (list comparer tree-root)))))
(define rc-of
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () (empty-tree))
     (search-tree-structure
      (k d h lc rc)
      rc) ) ) )
(define lc-of
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () (empty-tree))
     (search-tree-structure
      (k d h lc rc)
      lc) ) ) )
(define key-of
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () (empty-tree))
     (search-tree-structure
      (k d h lc rc)
      k) ) ) )
(define height-of
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () -1)
     (search-tree-structure
      (k d h lc rc)
      h) ) ) )
(define data-of
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () (empty-tree))
     (search-tree-structure
      (k d h lc rc)
      d) ) ) )
(define empty-tree?
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () #t)
     (search-tree-structure
      (k d h lc rc)
      #f) ) ) )

(define ts-lrotate
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () st) ;; corner-case of an empty tree.
     ;;
     ;; If the tree's not empty, then this derives a new
     ;; instance of a search-tree-structure that is an
     ;; "l-rotate" of that search tree:
     (search-tree-structure
      (key-part data-part height left-child right-child)
      (let*
          ((lc-of-rc (lc-of right-child))
           (rc-of-rc (rc-of right-child))
           (lc-height (height-of left-child))
           (lc-of-rc-height (height-of lc-of-rc))
           ;; The following is the definition of the new
           ;; left-hand child:
           (new-lc
            (search-tree-structure
             key-part
             data-part
             (+ 1 (max lc-height lc-of-rc-height) )
             left-child
             lc-of-rc) )
           (new-rc (rc-of right-child)) )
        (search-tree-structure
         (key-of right-child)
         (data-of right-child)
         (+ 1 (max (height-of new-lc) (height-of new-rc)))
         new-lc
         new-rc ) ) ) ) ) )

(define ts-rrotate
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () st) ;; corner-case of an empty tree.
     ;;
     ;; If the tree's not empty, then this derives a new
     ;; instance of a search-tree-structure that is an
     ;; "r-rotate" of that search tree:
     (search-tree-structure
      (key-part data-part height left-child right-child)
      (let*
          ((lc-of-lc (lc-of left-child))
           (rc-of-lc (rc-of left-child))
           (rc-height (height-of right-child))
           (rc-of-lc-height (height-of rc-of-lc))
           (new-lc lc-of-lc)
           ;; The following is the definition of the new
           ;; right-hand child:
           (new-rc
            (search-tree-structure
             key-part
             data-part
             (+ 1 (max rc-of-lc-height rc-height) )
             rc-of-lc
             right-child) ) )
        (search-tree-structure
         (key-of left-child)
         (data-of left-child)
         (+ 1 (max (height-of new-lc) (height-of new-rc)))
         new-lc
         new-rc) ) ) ) ) )

(define ts-rebalance
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () st)
     (search-tree-structure
      (key-part data-part height left-child right-child)
      (let*
          ((lc-height (height-of left-child))
           (rc-height (height-of right-child)) )
        (cond
         ((> (abs (- lc-height rc-height)) 1)
          (cond
           ((< lc-height rc-height)
            (let*
                ((lc-of-rc (lc-of right-child))
                 (rc-of-rc (rc-of right-child)) )
              (ts-lrotate
               (cond
                ((<= (height-of lc-of-rc) (height-of rc-of-rc)) st)
                ((>  (height-of lc-of-rc) (height-of rc-of-rc))
                 (let
                     ((new-rc (ts-rrotate right-child)))
                   (search-tree-structure
                    key-part
                    data-part
                    (+ 1 (max lc-height (height-of new-rc)) )
                    left-child
                    new-rc ) ) ) ) ) ) )
           ((> lc-height rc-height)
            (let*
                ((lc-of-lc (lc-of left-child))
                 (rc-of-lc (rc-of left-child)))
              (ts-rrotate
               (cond
                ((<= (height-of rc-of-lc) (height-of lc-of-lc)) st)
                ((>  (height-of rc-of-lc) (height-of lc-of-lc))
                 (let
                     ( (new-lc (ts-lrotate left-child)) )
                   (search-tree-structure
                    key-part
                    data-part
                    (+ 1 (max (height-of new-lc) rc-height) )
                    new-lc
                    right-child) ) ) ) ) ) ) ))
         (else st) ) ) ) ) ) )

(define ts-lookup
  (lambda (ts sk)
    (letrec
        ((st-lookup-inner
          (lambda (root sk ord-pred?)
            (cases
             search-tree root
             (empty-tree () '())
             (search-tree-structure
              (key-part data-part height left-child right-child)
              (cond ((ord-pred? sk key-part)
                     (st-lookup-inner left-child sk ord-pred?))
                    ((ord-pred? key-part sk)
                     (st-lookup-inner right-child sk ord-pred?))
                    (else (list key-part data-part)) ) ) ) ) ) )
      (cases
       tree-set ts
       (tree-set-structure
        (comparer tree-root)
        (st-lookup-inner tree-root (key-datum sk) comparer)) ) ) ) )

(define num-comp
  (lambda (x y)
    (cases
     key-type x
     (key-datum
      (internal-x)
      (cases
       key-type y
       (key-datum
        (internal-y)
        (< internal-x internal-y)) ) ) ) ) )



;; This is not the most efficient way to solve this problem, but it will have to do
;; for now.  The other avl-tree code provides some insights into doing this better,
;; but right now I'm just trying to keep up the cognitive rethinking that the
;; define-datatype and cases tools present to me.  They're a boon and a bane,
;; all at the same time, eh?  Still, programming in Scheme imposes much lower
;; friction that other notations, even with the cognitive re-wiring I'm having
;; to do just to handle the EOPL2e lessons I'm working through!
(define ts-inorder
  ;; Inorder traversal of a tree-set, to put the stuff into a list
  ;; for use by other processing?
  (lambda (ts)
    (letrec
        ((ts-inner-inorder
          (lambda (root)
            (cases
             search-tree root
             (empty-tree () '())
             (search-tree-structure
              (key-part data-part height left-child right-child)
              (let*
                  ((curr-key
                    (cases
                     key-type key-part
                     (key-datum
                      (internal-key)
                      internal-key)))
                   (left-result
                    (ts-inner-inorder left-child))
                   (right-result
                    (ts-inner-inorder right-child)))
                ;; It's the use of append that can be expensive.  There are
                ;; othere techniques which are more efficient.
                (append left-result (cons curr-key '()) right-result)) ) ) ) ) )
      (cases
       tree-set ts
       (tree-set-structure
        (comparer tree-root)
        (ts-inner-inorder tree-root))))) )



(define ts-big
  (lambda (ts n limit)
    (cond ((> n limit) ts)
          (else (ts-big (ts-insert ts (key-datum n) (datum '())) (+ n 1) limit)) ) ) )

(define find-min
  (lambda (st)
    (cases
     search-tree st
     (empty-tree () st)
     (search-tree-structure
      (key-part data-part height left-child right-child)
      (cond
       ((empty-tree? left-child) st)
       (else (find-min left-child) ) ) ) ) ) )

(define ts-delete
  (lambda (ts k)
    (letrec
        ((ts-delete-inner
          (lambda (st sk ord-pred?)
            (cases
             search-tree st
             (empty-tree () st)
             (search-tree-structure
              (key-part data-part height left-child right-child)
              (cond
               ((ord-pred? sk key-part)
                (let
                    ((new-lc (ts-delete-inner left-child sk ord-pred?)))
                  (ts-rebalance
                   (search-tree-structure
                    key-part
                    data-part
                    (+ 1 (max (height-of new-lc) (height-of right-child)))
                    new-lc
                    right-child)) ) )
               ((ord-pred? key-part sk)
                (let
                    ((new-rc (ts-delete-inner right-child sk ord-pred?)))
                  (ts-rebalance
                   (search-tree-structure
                    key-part
                    data-part
                    (+ 1 (max (height-of left-child) (height-of new-rc)))
                    left-child
                    new-rc)) ) )
               (else
                ;; the key in question, sk, is in the root of the search tree, st.
                (cond
                 ((and (empty-tree? right-child) (empty-tree? left-child))
                  (empty-tree))
                 (else
                  (let*
                      ;; Special case needed when there is not
                      ;; a right-hand subtree from which to retrieve
                      ;; a replacement for the key to be deleted.
                      ;; When that happens, then new key comes from the left
                      ;; subtree, which can only be a leaf.
                      ((new-node
                        (cond
                         ((empty-tree? right-child) left-child)
                         (else (find-min right-child))) )
                       (new-rc
                        (cond
                         ((empty-tree? right-child) (empty-tree) )
                         (else
                          (ts-delete-inner right-child (key-of new-node) ord-pred?)) ) )
                       (new-lc
                        (cond
                         ((empty-tree? right-child) (empty-tree))
                         (else left-child) ) ) )
                    (ts-rebalance
                     (search-tree-structure
                      (key-of new-node)
                      (data-of new-node)
                      (+ 1 (max (height-of new-lc) (height-of new-rc)) )
                      new-lc
                      new-rc) ) ) ) ) ) ) ) ) ) ) )
      (cases
       tree-set ts
       (tree-set-structure
        (comparer tree-root)
        (tree-set-structure
         comparer
         (ts-delete-inner tree-root (key-datum k) comparer))) ) ) ) )

(define st-rconcat-key
  (lambda (stl str sk sd)
    (let*
        ((height-eq (equal? (height-of stl) (height-of str)) )
         (height-gt (>      (height-of stl) (height-of str)) )
         (new-key (cond ((or height-gt height-eq) sk)
                        (else (key-of str))) )
         (new-data (cond ((or height-gt height-eq) sd)
                         (else (data-of str)) ) )
         (new-str (cond ((or height-gt height-eq) str)
                       (else (rc-of str)) ) )
         (new-stl (cond ((or height-gt height-eq) stl)
                        (else (st-rconcat-key stl (lc-of str) sk sd) ) )) )
      (ts-rebalance
       (search-tree-structure
        new-key
        new-data
        (+ 1 (max (height-of new-stl) (height-of new-str)) )
        new-stl
        new-str) ) ) ) )

(define st-lconcat-key
  (lambda (stl str sk sd)
    (let*
        ((height-eq (equal? (height-of stl) (height-of str)))
         (height-gt (<      (height-of stl) (height-of str)))
         (new-key (cond ((or height-gt height-eq) sk)
                        (else (key-of stl))) )
         (new-data (cond ((or height-gt height-eq) sd)
                         (else (data-of stl)) ) )
         (new-str (cond ((or height-gt height-eq) str)
                        (else (st-lconcat-key (rc-of stl) str sk sd)) ) )
         (new-stl (cond ((or height-gt height-eq) stl)
                        (else (lc-of stl)) ) ) )
      (ts-rebalance
       (search-tree-structure
        new-key
        new-data
        (+ 1 (max (height-of new-stl) (height-of new-str)))
        new-stl
        new-str)) ) ) )

(define ts-split
  (lambda (ts k)
    (cases
     tree-set ts
     (tree-set-structure
      (comparer tree-root)
      (letrec
          ((ts-split-i
            (lambda (st sk ord-pred?)
              (cond ((ord-pred? sk (key-of st))
                     (let ((sr (ts-split-i (lc-of st) sk ord-pred?)))
                       (cons
                        (car sr)
                        (st-rconcat-key (cdr sr) (rc-of st) (key-of st) (data-of st)) ) ) )
                    ((ord-pred? (key-of st) sk)
                     (let ((sr (ts-split-i (rc-of st) sk ord-pred?) ) )
                       (cons
                        (st-lconcat-key (lc-of st) (car sr) (key-of st) (data-of st))
                        (cdr sr)) ) )
                    (else ;; the two keys are equal
                     (cons (lc-of st) (rc-of st)) ) ) ) ) )
        (let
            ( (result (ts-split-i tree-root (key-datum k) comparer) ) )
          (cons
           (tree-set-structure
            comparer
            (car result))
           (tree-set-structure
            comparer
            (cdr result) ) ) ) ) ) ) ) )            
      

;;,pretty-print
  (ts-insert
   (ts-insert
    (ts-insert
     (tree-set-structure
      num-comp
      (empty-tree))
     (key-datum 0)
     (datum "some data"))
    (key-datum 1)
    (datum "more data"))
   (key-datum 2)
   (datum "third record"))