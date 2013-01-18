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
(define (appendRseq s i j)
  (cond [(eq? i j) s]
        [#t (appendRseq (appendR s (+ i 1)) (+ 1 i) j)])
  )
;;
;; 
;;
;; This appendRv function uses the more usual "build up the list
;; via multiple calls to cons, then reverse the final result
;; in order to get the list ordered the way we want" approach.
;; I was interested in comparing the performance of the two
;; approaches.
(define (appendRv s i j)
  (cond [(eq? i j) (reverse s)]
        [#t (appendRv (cons (+ i 1) s) (+ i 1) j)]
        )
  )

;; One can see results like these:
;; > (define big-list-1 (appendRseq (appendR idf 1) 1 1000000))
;> (time (length (big-list-1 ())))
;cpu time: 1056 real time: 1504 gc time: 868
;1000000
;> (time (length (big-list-1 ())))
;cpu time: 136 real time: 141 gc time: 0
;1000000
;> (time (length (big-list-1 ())))
;cpu time: 3972 real time: 4636 gc time: 3696
;1000000
;> (time (length (big-list-1 ())))
;cpu time: 140 real time: 143 gc time: 0
;1000000
;> (time (length (big-list-1 ())))
;cpu time: 132 real time: 142 gc time: 0
;1000000
;> (time (length (big-list-1 ())))
;cpu time: 624 real time: 815 gc time: 408
;1000000
;> (time (length (appendRv '(1) 1 1000000)))
;cpu time: 1192 real time: 1595 gc time: 648
;1000000
;> (time (length (appendRv '(1) 1 1000000)))
;cpu time: 1136 real time: 1263 gc time: 632
;1000000
;> (define big-list-end ((appendRseq (appendR idf (+ 1000000 1)) (+ 1000000 1) (+ 1000000 100000)) () ))
;> (length big-list-end)
;100000
;;
;> (define big-list-end ((appendRseq (appendR idf (+ 1000000 1)) (+ 1000000 1) (+ 1000000 1000000)) () ))
;> (time (length (big-list-1 big-list-end)))
;cpu time: 984 real time: 1184 gc time: 748
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1480 real time: 2042 gc time: 780
;2000000
;> (time (length (big-list-1 big-list-end)))
;cpu time: 440 real time: 552 gc time: 208
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 7184 real time: 8477 gc time: 6488
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 5337 real time: 6203 gc time: 4717
;2000000
;> (time (length (big-list-1 big-list-end)))
;cpu time: 536 real time: 687 gc time: 304
;2000000
;;
;> (time (length ((appendRseq big-list-1 (+ 1000000 1) (+ 1000000 1000000)) ()) ))
;cpu time: 1637 real time: 1905 gc time: 920
;1999999
;> (time (length ((appendRseq big-list-1 (+ 1000000 1) (+ 1000000 1000000)) ()) ))
;cpu time: 1312 real time: 1533 gc time: 600
;1999999
;> (time (length (big-list-1 ())))
;cpu time: 132 real time: 135 gc time: 0
;1000000
;> (time (length ((appendRseq big-list-1 1000000 (+ 1000000 1000000)) ()) ))
;cpu time: 2168 real time: 2419 gc time: 1448
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1252 real time: 1571 gc time: 644
;2000000
;> (time (length ((appendRseq big-list-1 1000000 (+ 1000000 1000000)) ()) ))
;cpu time: 1360 real time: 1624 gc time: 668
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1696 real time: 2202 gc time: 984
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 6032 real time: 7100 gc time: 5392
;2000000
;> (time (length ((appendRseq big-list-1 1000000 (+ 1000000 1000000)) ()) ))
;cpu time: 1296 real time: 1433 gc time: 604
;2000000
;> (time (length (big-list-1 big-list-end)))
;cpu time: 152 real time: 157 gc time: 0
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1552 real time: 1716 gc time: 984
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1376 real time: 1720 gc time: 812
;2000000
;> (time (length (big-list-1 big-list-end)))
;cpu time: 344 real time: 454 gc time: 128
;2000000
;> (time (length (big-list-1 big-list-end)))
;cpu time: 644 real time: 671 gc time: 464
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1300 real time: 1606 gc time: 700
;2000000
;> (time (length (append (appendRv '(1) 1 1000000) big-list-end)))
;cpu time: 1509 real time: 1816 gc time: 900
;2000000
;> (time (length (big-list-1 big-list-end)))
;cpu time: 196 real time: 304 gc time: 0
;2000000
;;
;> (time (letrec [ (find-end (lambda (l) (cond [(eq? () (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 600 real time: 2332 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(eq? () (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1424 real time: 1592 gc time: 548
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(eq? () (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 428 real time: 496 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(eq? () (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1652 real time: 2024 gc time: 780
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(eq? () (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1352 real time: 1583 gc time: 472
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(eq? () (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 1152 real time: 1298 gc time: 664
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 988 real time: 1137 gc time: 488
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 448 real time: 495 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 468 real time: 698 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1292 real time: 1495 gc time: 452
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 1288 real time: 1605 gc time: 796
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 1064 real time: 1431 gc time: 536
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 6041 real time: 6707 gc time: 5128
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 464 real time: 681 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1688 real time: 1871 gc time: 844
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 800 real time: 1025 gc time: 284
;2000000
;;
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 876 real time: 958 gc time: 392
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 2181 real time: 2379 gc time: 1289
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1532 real time: 1663 gc time: 704
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1648 real time: 1765 gc time: 828
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 5308 real time: 5583 gc time: 4780
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 4545 real time: 4751 gc time: 4057
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 452 real time: 508 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 440 real time: 487 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 420 real time: 448 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1612 real time: 1738 gc time: 804
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 732 real time: 830 gc time: 252
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 2388 real time: 2617 gc time: 1500
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 448 real time: 514 gc time: 0
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (append (appendRv '(a) 1 1000000) big-list-end)) ) )
;cpu time: 1540 real time: 1638 gc time: 704
;2000000
;> (time (letrec [ (find-end (lambda (l) (cond [(null? (cdr l)) (car l)] [#t (find-end (cdr l))] ) )) ] (find-end (big-list-1 big-list-end))) )
;cpu time: 440 real time: 459 gc time: 0
;2000000
