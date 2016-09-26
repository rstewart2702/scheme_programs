;; The Haskell was:
;; composeTransforms :: [a -> a] -> a -> a
;; composeTransforms = flip (foldr ($))
;;
;; so:
;;   composeTransforms [(+7), (*10)] 3
;; yields:
;;   37
;; and
;;   composeTransforms [(\_ -> 42)] 0
;; yields
;;   42
;; and
;;   composeTransforms [] "cats"
;; yields
;;   "cats"
;;
;; In F#, you might write:
;;   let dollarApply f x =
;;       f x
;;
;;   let flip f x y = f y x
;;
;;   let foldr fcn =
;;       (flip (List.foldBack fcn))
;;
;;   let composedTransforms itm loi =
;;       (flip (foldr dollarApply)) itm loi
;;
;; and this is because the ordering of the arguments to List.foldBack,
;; the equivalent of foldr, is DIFFERENT FROM EVERYBODY ELSE'S!
;; Vide, the signature is:
;;   (('a -> 'b -> 'b) -> 'a list -> 'b -> 'b)
;; instead of:
;;   (('a -> 'b -> 'b) -> 'b -> 'a list -> 'b)
;; Good grief.
;;
;; So, the definition of foldr creates a function whose signature is:
;;   fcn:('a -> 'b -> 'b) -> ('b -> 'a list -> 'b)
;; so that (foldr dollarApply) is a function with signature:
;;   ('b -> 'a list -> 'b)
;; so that (fun loi itm -> (flip (foldr dollarApply)) loi itm) has signature:
;;   loi:(('a -> 'a) list) -> itm: 'a -> 'a
;; right?

(define flip
  (lambda (fcn x y)
    (fcn y x)))

(define dollar-apply
  (lambda (fcn x)
    (fcn x)))

(define foldr-curried
  (lambda (fcn)
    (lambda (init-item lst) (foldr fcn init-item lst)) ) )

; foldr has a "signature" like:
;   (foldr <proc> <init> <lst>)
; where <proc> is a function, <init> is an initial value, and <lst> is a "list o'stuff"
; to which the function gets applied, combining the init value and the list elements,
; "initially," pun-intended...


(define flip-curried
  (lambda (fcn)
    (lambda (x y) (flip fcn x y))))

;; This does in scheme what the composeTransforms definition did above
;; in Haskell.  In Scheme, our "currying" is made more explicit:
(define compose-transforms
  (lambda (input-list-of-functions item)
    ( (flip-curried (foldr-curried dollar-apply)) input-list-of-functions item ) ) )

(define compose-transforms2
  (lambda (input-list-of-functions item)
    ( (curry flip (curry foldr dollar-apply)) input-list-of-functions item) ) )

(define plus-7
  (lambda (x) (+ 7 x) ) )
(define times-10
  (lambda (x) (* 10 x) ) )

(compose-transforms
 (list plus-7 times-10)
 3)
;; should yield 37
;; which is:
;;   ((lambda (x) (+ 7 x)) ((lambda (x) (* 10 x)) 3))

;; So, I guess this just goes to show that Haskell code can become
;; a bit pedantic, but really, this is a documentation issue as much
;; as anything else, isn't it?  The above Haskell example simply
;; demonstrates that it's possible to be kind of impenetrable in any
;; language, especially when you refuse to write comments and
;; documentation.
