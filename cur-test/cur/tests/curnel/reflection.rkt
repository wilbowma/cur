#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  (except-in "../../../../cur-lib/cur/curnel/turnstile/equiv.rkt" cur-equal?)
  "../../../../cur-lib/cur/curnel/turnstile/stxutils.rkt"
 ; "../../../../cur-lib/cur/curnel/racket-impl/reflection.rkt"
  "../../../../cur-lib/cur/curnel/turnstile/reflection.rkt"
  )
 "../../../../cur-lib/cur/curnel/turnstile/cur-to-turnstile.rkt"
; "../../../../cur-lib/cur/curnel/racket-impl/type-check.rkt"
 ;"../../../../cur-lib/cur/curnel/racket-impl/runtime.rkt"
 ;"runtime.rkt"
 turnstile/examples/dep-ind-cur
 (only-in turnstile/lang infer))

(turn-data Nat2 : 0 (turn-Type 0)
        (z2 :   Nat2)
        (s2 : (turn-Π (x : Nat2) Nat2)))
(turn-data Maybe : 1 (turn-Π (A : (turn-Type 0)) (turn-Type 0))
        (none : (turn-Π (A : (turn-Type 0)) (Maybe A)))
        (just : (turn-Π (A : (turn-Type 0)) (turn-Π (a : A) (Maybe A)))))
(turn-axiom Kittens : (turn-Type 0))
(begin-for-syntax 
  (define (cur-equal? term1 term2)
    (equal? (syntax->datum term1) (syntax->datum term2)))
  ;(displayln (format "testing data-ref-name for z2's type: ~a\n\n" (syntax-property (car (cadddr (infer (list #'z2) ))) 'data-ref-name)))
  ;(displayln (format "testing c-ref-name for z2 id: ~a, ref-name: ~a\n\n" (local-expand #'z2 'expression null) (syntax-property (local-expand #'z2 'expression null) 'c-ref-name)))
  ;(displayln (format "inferring none: ~a\n\n" (syntax->datum (car (cadddr (infer (list #'none) ))))))
  (chk
   #:eq cur-equal? (cur-type-infer #'(turn-Type 0)) #'(turn-Type 1)
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-Π (x : (turn-Type 0)) (turn-Type 0))
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) x)) #'(turn-Π (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) (turn-Π (x : (turn-Type 0)) (turn-Type 0)))
   #:x (cur-type-infer #'a) "a: unbound"
   #:eq cur-equal? (cur-type-infer #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 1)
   #:eq cur-equal? (cur-type-infer #'z2) #'Nat2 
   #:eq cur-equal? (cur-type-infer #'s2) #'(turn-Π (x : Nat2) Nat2)  
   #:eq cur-equal? (cur-type-infer #'none) #'(turn-Π (A : (turn-Type 0)) (Maybe A)) 
   #:eq cur-equal? (cur-type-infer #'just) #'(turn-Π (A : (turn-Type 0)) (turn-Π (a : A) (Maybe A)))
   #:eq cur-equal? (cur-type-infer #'Kittens) #'(turn-Type 0)
   )
 (chk
   #:t (cur-type-check? #'(turn-λ (x : (turn-Type 0)) x)  #'(turn-Π (x : (turn-Type 0)) (turn-Type 0))) 
   #:t (cur-type-check? #'(turn-Type 0) #'(turn-Type 1))
   #:t (cur-type-check? #'z2 #'Nat2)
   #:t (cur-type-check? #'s2 #'(turn-Π (x : Nat2) Nat2))
   #:t (cur-type-check? #'Kittens #'(turn-Type 0))
   )
 (chk
  #:= (cur->datum #'(turn-Type 0)) '(turn-Type 0)
  #:= (cur->datum #'(turn-λ (a : (turn-Type 0)) a)) '(turn-λ (a : (turn-Type 0)) a) 
  #:= (cur->datum #'(turn-Π (a : (turn-Type 0)) (turn-Type 0))) '(turn-Π (a : (turn-Type 0)) (turn-Type 0))
  ;#:= (cur->datum #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) '(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0)) ;fails bc evaluation
  #:= (cur->datum #'(turn-app s2 z2)) '(turn-app s2 z2)
  #:= (cur->datum #'(turn-app s2 (turn-app s2 z2))) '(turn-app s2 (turn-app s2 z2))
  #:= (cur->datum #'(turn-app just Nat2)) '(turn-app just Nat2)
  )
 (chk
  #:eq cur-equal? (cur-normalize #'(turn-Type 1)) #'(turn-Type 1)
  #:eq cur-equal? (cur-normalize #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-λ (x : (turn-Type 0)) x) 
  #:eq cur-equal? (cur-normalize #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 0)
  #:eq cur-equal? (cur-normalize #'(((turn-λ (A : (turn-Type 3)) (turn-λ (a : (turn-Type 2)) a)) (turn-Type 2)) (turn-Type 1))) #'(turn-Type 1) ))