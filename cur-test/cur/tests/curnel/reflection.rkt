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
  #;(displayln (syntax-property (local-expand #'(turn-λ (a : (turn-Type 0)) a) 'expression null) ':))
  #;(displayln (local-expand #'(turn-Type 0) 'expression null))
  (define (cur-equal? term1 term2)
    (equal? (syntax->datum term1) (syntax->datum term2)))
 (chk
   #:eq cur-equal? (cur-type-infer #'(turn-Type 0)) #'(turn-Type 1)
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-Π (x : (turn-Type 0)) (turn-Type 0))
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) x)) #'(turn-Π (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) (turn-Π (x : (turn-Type 0)) (turn-Type 0)))
   #:x (cur-type-infer #'a) "a: unbound"
   #:eq cur-equal? (cur-type-infer #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 1)
   )
 (chk
   #:t (cur-type-check? #'(turn-λ (x : (turn-Type 0)) x)  #'(turn-Π (x : (turn-Type 0)) (turn-Type 0))) ;expected and inferred are (turn-Π (x : (turn-Type 0)) (turn-Type 0)), but typecheck? returns #f
   #:t (cur-type-check? #'(turn-Type 0) #'(turn-Type 1))
   )
 (chk

  #:= (cur->datum #'(turn-Type 0)) '(turn-Type 0)
  #:= (cur->datum #'(turn-λ (a : (turn-Type 0)) a)) '(turn-λ (a : (turn-Type 0)) a) ;fails at dep-ind-cur: bad syntax in (lambda (a) a)
  #:= (cur->datum #'(turn-Π (a : (turn-Type 0)) (turn-Type 0))) '(turn-Π (a : (turn-Type 0)) (turn-Type 0))
  )
 (chk
  #:eq cur-equal? (cur-normalize #'(turn-Type 1)) #'(turn-Type 1)
  #:eq cur-equal? (cur-normalize #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-λ (x : (turn-Type 0)) x) ;fails at dep-ind-cur: bad syntax in (lambda (x) x)
  #:eq cur-equal? (cur-normalize #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 0)
  #:eq cur-equal? (cur-normalize #'(((turn-λ (A : (turn-Type 3)) (turn-λ (a : (turn-Type 2)) a)) (turn-Type 2)) (turn-Type 1))) #'(turn-Type 1) ))
