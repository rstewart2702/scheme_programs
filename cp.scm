(define cp1
  (lambda (d p)
    (let ( (fctr (+ 1.0 p)) )
      (* d fctr fctr) ) ) )

(define cp2
  (lambda (d p)
    (let ( (fctr (+ 1.0 p)) )
      (+ (* d fctr)
	 (* d p p) ) ) ) )

;; In order for this, especially, to make sense, we must
;; have (< (abs p) 1).
;; The geometric series sums to (/ 1.0 (- 1.0 p))
;;
;; The reasoning is based on the following problem:
;;   What is the solution to:
;;      fee = pct * (fee + dep)
;;   == fee = pct * fee + pct * dep
;;   == fee - pct * fee = pct * dep
;;   == fee * (1 - pct) = pct * dep
;;   == fee = (pct * dep) / (1 - pct)
;;   ==> fee = pct * (dep / (1 - pct)) && fee + dep = (dep / (1 - pct))
;; This is consistent with the definition of the geometric
;; series, and tells us what our total needs to be if we
;; wish to compensate for transaction processing fees which
;; are a percentage (pct, above) of the transaction amount,
;; and we know what we want the seller to end up having after
;; the transaction processor gets their fees (which is
;; dep, above.)
(define cp3
  (lambda (d p)
    (/ d (- 1.0 p)) ) )
;;    (* d (/ 1 (- 1.0 p))) ) )