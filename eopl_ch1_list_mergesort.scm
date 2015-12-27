;; This appendR function, along with the idf identity function,
;; gives us a way to append to lists in O(1) time by 
;; implementing list append as function composition.
;; Then, list concatenation becomes a matter of passing the list
;; to be appended to the function-that-is-the-first-part-of-the-list.
;; And the cost is linear in the number of calls which are made
;; by that function-that-is-the-first-part-of-the-list.  We sort of
;; defer the work of building the list in the correct order until
;; the precise time at which we need to actually see the list.
;;
;; This approach to lists is the functional languages version
;; of "difference lists."
;;
(define (appendR hpf i) [ lambda (h) [ hpf (cons i h) ] ] )
(define idf (lambda (x) x))
;; Thus the idea is:
;;   ((appendR idf 'a) ()) == (a)
;; because 
;; ( (lambda (h) ([lambda (x) x] (cons 'a h))) () )
;; == 
;;   ( [lambda (x) x] (cons 'a ()) )
;; ==
;;   (cons 'a ())
;; ==
;;   (a)



; Exercise 1.28
; Support procedures to help with "sort" specified by exercise 1.28:
(define partitiontr
  (lambda (item ilist listl listr)
    (cond
      [ (null? ilist) 
          (cons listl (cons listr '())) ]
      [ (<= item (car ilist))
          (partitiontr item (cdr ilist) listl (cons (car ilist) listr) ) ]
      [ (< (car ilist) item)
          (partitiontr item (cdr ilist) (cons (car ilist) listl) listr) ] ) ) )

(define partition
  (lambda (item ilist)
    (partitiontr item ilist '() '()) ) )

(define list-pick
  (lambda (l n)
    (cond [(eqv? n 1) (car l)]
          [#t (list-pick (cdr l) (- n 1)) ] ) ) )

;; median-of-three
;; At the cost of linear-time scans of the list passed in, this
;; function tries to calculate a "median of three" elements
;; from the list-of-integers in order to help balance the 
;; performance of the qsortloi and prevent its performance from
;; degrading so badly when its handed a sorted or nearly-sorted
;; list-of-integers.
(define median-of-three
  (lambda (l)
    (let 
        ( [ item-1st (car l) ]
          [ item-mid (list-pick l (quotient (length l) 2)) ]
          [ item-end (list-pick l (length l)) ] )
      (cond 
        [ (and (<= item-1st item-end) (<= item-1st item-mid) (<= item-mid item-end)) item-mid ]
        [ (and (<= item-1st item-end) (<= item-1st item-mid) (<= item-end item-mid)) item-end ]
        ;
        [ (and (<= item-mid item-1st) (<= item-mid item-end) (<= item-1st item-end)) item-1st ]
        [ (and (<= item-mid item-1st) (<= item-mid item-end) (<= item-end item-1st)) item-end ]
        ;
        [ (and (<= item-end item-1st) (<= item-end item-mid) (<= item-1st item-mid)) item-1st ]
        [ (and (<= item-end item-1st) (<= item-end item-mid) (<= item-mid item-1st)) item-mid ] ) ) ) )


;; Quicksort-style sort of an "loi," "list-of-integers":
;; Hoare's quicksort on Lisp lists seems to have a very natural
;; expression in Scheme, since the algorithm itself is very
;; recursive in nature, or finds its most natural expression in
;; those terms.
(define qsortloi
  (lambda (loi)
    (cond 
      [ (null? loi) 
        () ]
      [ (null? (cdr loi)) 
        loi ]
      [ #t 
        (let
            [ (two-partitions 
               (cond [(>= (length loi) 3) (partition (median-of-three (cdr loi)) (cdr loi))]
                     [#t (partition (car loi) (cdr loi)) ]) ) ]
            (merge 
             (cons (car loi) () )
             (append
               (qsortloi (car two-partitions) )
               (qsortloi (cadr two-partitions) ) ) ) ) ] ) ) )

;; Mergesort-related functions:

; Function composition combinator:
(define my-compose
  (lambda (f g)
    [lambda (x) (f (g x))] ) )

; Function ra-item derives a new list-item-as-a-function.
; Such can then be composed with other such functions
; so that we may build up a list structure which does
; not require a call to reverse to derive an appropriately
; ordered list structure.
(define ra-itm
  (lambda (itm)
    (lambda (h) (cons itm h)) ) )

; Function append-r adds list items to the end of a
; list in constant time, instead of linear-time invocations
; of the append function.
; In order to derive the final list, we must simply 
; pass a null list to the function in order to derive
; the needed list structure.
(define append-r
  (lambda (lf itm)
    (compose lf itm) ) )

;; split-list-tr
;; Tail-recursive auxilliary function to calculate the 
;; list-split by appending the first n elements of l2 onto 
;; l1.  In the case that there are not any more elements
;; to append, i.e., n = 0, then the first list, which is
;; actually a curried function, is invoked on the empty
;; list, (), to "fill the hole" and convert l1 back into 
;; a "standard list" which is expected by the client of
;; the driving function, split-list.
(define split-list-tr
  (lambda (n l1 l2)
    (cond
      ; [(eqv? n 0) (cons l1 (cons l2 ())) ]
      [ (eqv? n 0) (cons (l1 ()) (cons l2 ())) ]
      [ #t (split-list-tr (- n 1) (append-r l1 (ra-itm (car l2))) (cdr l2) ) ] ) ) )
      ; [#t (split-list-tr (- n 1) (appendR l1 (car l2)) (cdr l2)) ] ) ) )
      ; [#t (split-list-tr (- n 1) (cons (car l2) l1) (cdr l2)) ] ) ) )

;; split-list
;; Wrapper around the tail-recursive list-splitter, split-list-tr.
;; This function sets up the first list parameter of split-list-tr 
;; by deriving the "one-element list-with-a-hole."
(define split-list
  (lambda (n l)
    (cond 
      [ ; This is a corner case.
       (eqv? n 0) (cons () (cons l ())) ]
      [ ; This is the more general case for which the tail-recursive
        ; function is used, and "(appendR idf (car l))" is a list
        ; which preserves the order of the data appended to it.
        ; #t (split-list-tr (- n 1) (appendR idf (car l)) (cdr l)) ]
        (split-list-tr (- n 1) (ra-itm (car l)) (cdr l)) ]
      ) ) )

; (define split-list
;   (lambda (n l)
;     (split-list-tr n () l)))

;; merge
;; Merges together two already-ordered lists into one resulting list.
(define merge
  (lambda (l1 l2)
    (cond
      [ (null? l1) l2 ]
      [ (null? l2) l1 ]
      [ (<= (car l1) (car l2))
          (cons (car l1) (merge (cdr l1) l2)) ]
      [ #t
          (cons (car l2) (merge l1 (cdr l2))) ] ) ) )

(define mergesortloi
  (lambda (l)
    ; (printf "Starting list:  ~a~n" l)
    (cond
      [ (null? l) () ]
      [ (null? (cdr l)) l ]
      [ (and (null? (cddr l)) (<  (car l) (cadr l)) ) l]
      [ (and (null? (cddr l)) (<= (cadr l) (car l)) ) (cons (cadr l) (cons (car l) () )) ]
      [ #t
        (let ((two-lists (split-list (quotient (length l) 2) l) ) )
          ; (printf "After split:  ~a~n" two-lists)
          (merge (mergesortloi (car two-lists) )
                 (mergesortloi (cadr two-lists)))) ] ) ) )

(define mergesortloi-nice
  (lambda (l)
    (cond
      ((null? l) '())
      (else
       (let* ((l-tail (cdr l))
              (l-first (car l))
              (l-second (if (null? l-tail) '() (cadr l)))
              (l-third (if (null? l-second) '() (cddr l))) )
         (cond
           ((null? l-tail) ;; Is the list only one element long?
            l)
           ((and (null? l-third) ;; the list is only two elements long AND
                 (< l-first l-second) ) ; the two elements are already in order
            l) ;; return the sorted list
           ((and (null? l-third) ;; the list is only two elements long AND
                 (<= l-second l-first) ) ;; the two elements are out of order
            (list l-second l-first))
           ;; this is the more general case:
           (else
            (let
                ((two-lists (split-list (quotient (length l) 2) l)))
              (merge (mergesortloi-nice (car two-lists))
                     (mergesortloi-nice (cadr two-lists)) ) ) )
           ) ) ) ) ) )
                 
             

(define mergesortloi2
  (lambda (l)
    ; (printf "Starting list:  ~a~n" l)
    (cond
      [ (null? l) () ]
      [ (null? (cdr l)) l ]
      [ (and (null? (cddr l)) (<  (car l) (cadr l)) ) l]
      [ (and (null? (cddr l)) (<= (cadr l) (car l)) ) (cons (cadr l) (cons (car l) () )) ]
      [ #t
        (let ((two-lists (split-list (quotient (length l) 2) l) ) )
          ; (printf "After split:  ~a~n" two-lists)
          (merge (mergesortloi2 (reverse (car two-lists)))
                 (mergesortloi2 (cadr two-lists)))) ] ) ) )

(define make-big-list
  (lambda (ubound)
    (letrec 
        [ (genlist
           (lambda (limit newlist)
             (cond 
               [ (= limit 0) newlist ]
               [ #t (genlist (- limit 1) (cons (random ubound) newlist)) ] ) ) ) ]
      (genlist ubound ()) ) ) )

(define first-n
  (lambda (lst n)
    (letrec
        [(fn-tr
          (lambda (lst n bl)
            (cond [(eqv? n 0) (bl ())]
                  [#t (fn-tr (cdr lst) (- n 1) (append-r bl (ra-itm (car lst)))) ] ) ) )]
      (cond 
        [(null? lst) ()]
        [#t (fn-tr (cdr lst) (- n 1) (ra-itm (car lst))) ] ) ) ) )
