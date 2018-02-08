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
 turnstile/examples/dep-ind-cur )



(begin-for-syntax
  (define (cur-equal? term1 term2)
    (equal? (syntax->datum term1) (syntax->datum term2)))
 (chk 
   #:eq cur-equal? (cur-type-infer #'(turn-Type 0)) #'(Type 1) 
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Type 0)) x)) #'(Π (x : (Type 0)) (Type 0))
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) x)) #'(Π (x : (Π (x : (Type 0)) (Type 0))) (Π (x : (Type 0)) (Type 0)))
   #:x (cur-type-infer #'a) "a: unbound"
   #:eq cur-equal? (cur-type-infer #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(Type 1)
   )
#; (chk
   #:t (cur-type-check? #'(turn-λ (x : (turn-Type 0)) x)  #'(Π (x : (Type 0)) (Type 0))) ;fails typecheck?
   #:t (cur-type-check? #'(turn-Type 0) #'(Type 1))
   )
 (chk
  #:= (cur->datum #'a) 'a
  #:= (cur->datum #'(turn-Type 0)) '(Type 0)
  #:= (cur->datum #'(turn-λ (a : (turn-Type 0)) a)) '(λ (a : (Type 0)) a)
  ;#:= (cur->datum #'(turn-Π (a : (turn-Type 0)) (turn-Type 0))) '(Π (a : (Type 0)) (Type 0))
  )
 #;(chk
  #:eq cur-equal? (cur-normalize #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(Type 0)))
