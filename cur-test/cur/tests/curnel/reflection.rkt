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
 (chk 
   #:= (cur-type-infer #'(turn-Type 0)) #'(Type 1) 
   #:= (cur-type-infer #'(turn-λ (x : (turn-Type 0)) x)) #'(Π (x : (Type 0)) (Type 0))
   #:x (cur-type-infer #'a) "a: unbound"
   
 ;  #:t (cur-type-check? #'(turn-λ (x : (turn-Type 0) x)) #'(Π (x : (Type 0)) (Type 0)))
 ;  #:t (cur-type-check? #'(turn-Type 0) #'(Type 1))
     
;   #:= (cur->datum #'(turn-Type 0)) '(Type 0)
;   #:= (cur->datum #'(turn-λ (a : (turn-Type 0)) a)) '(λ (a : (Type 0)) a) ;?

#;#;#;   #:= (cur-normalize #'(turn-app (turn-λ (x : turn-Type) x) Bool)) #'Bool ))
