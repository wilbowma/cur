#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  (except-in cur/curnel/racket-impl/equiv cur-equal?)
  cur/curnel/racket-impl/stxutils
  cur/curnel/racket-impl/reflection)
 cur/curnel/racket-impl/type-check
 cur/curnel/racket-impl/runtime
; "runtime.rkt"
 )

(typed-data Nat : 0 (typed-Type 0)
  (z : Nat)
  (s : (typed-Π (x : Nat) Nat)))

(typed-data List : 1 (typed-Π (A : (typed-Type 0)) (typed-Type 0))
  (nil : (typed-Π (A : (typed-Type 0)) (typed-app List A)))
  (typed-cons : (typed-Π (A : (typed-Type 0)) (typed-Π (a : A) (typed-Π (r : (typed-app List A))
                                                                        (typed-app List A))))))

(begin-for-syntax
  (chk
   #:eq cur-equal? (cur-type-infer #'a #:local-env (list (cons #'a #'(cur-Type 0))))
   #'(typed-Type 0)
   #:x (cur-type-infer #'a) "a: unbound"
   #:x (cur-type-infer #'a #:local-env (list (cons #'a #'(typed-app
                                                          (cur-λ (cur-Type 0) (#%plain-lambda (x) x))
                                                          (cur-Type 0))))) "Expected term of type"

  #:eq cur-equal? (cur-method-type #'z #'(typed-λ (x : Nat) Nat))
  #'Nat

  #:eq cur-equal? (cur-method-type #'s #'(typed-λ (x : Nat) Nat))
  #'(typed-Π (x : Nat) (typed-Π (ih : Nat) Nat))

  #:eq cur-equal? (cur-method-type #'(nil Nat) #'(typed-λ (ls : (typed-app List Nat)) Nat))
  #'Nat

  #:eq cur-equal? (cur-method-type #'(typed-cons Nat) #'(typed-λ (ls : (typed-app List Nat)) Nat))
  #'(typed-Π (x : Nat) (typed-Π (ls : (typed-app List Nat)) (typed-Π (ih : Nat) Nat)))
  ))
