#lang racket/base

(require
 (for-syntax
  chk
  racket/base
  ;; TODO: replace with (require cur) at phase-0, when kernel is implemented
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

(cur-data Nat : 0 (cur-Type 0)
           (z :   Nat)
           (s : (cur-Π (x : Nat) Nat)))
(cur-data Maybe : 1 (cur-Π (A : (cur-Type 0)) (cur-Type 0))
           (none : (cur-Π (A : (cur-Type 0)) (Maybe A)))
           (just : (cur-Π (A : (cur-Type 0)) (cur-Π (a : A) (Maybe A)))))
(cur-data Vec : 1 (cur-Π (A : (cur-Type 0)) (cur-Π (n : Nat) (cur-Type 0)))
           (empty : (cur-Π (A : (cur-Type 0)) (Vec A z)))
           (cons : (cur-Π (A : (cur-Type 0))
                           (cur-Π (k : Nat)
                                   (cur-Π (x : A) (cur-Π (xs : (Vec A k))
                                                           (Vec A (s k))))))))
(cur-data Pair : 2 (cur-Π (A : (cur-Type 0)) (cur-Π (B : (cur-Type 0)) (cur-Type 0)))
           (make-pair : (cur-Π (A : (cur-Type 0)) (cur-Π (B : (cur-Type 0)) (Pair A B)))))
(cur-data Bool : 0 (cur-Type 0)
           (True : Bool)
           (False : Bool))
(define sub1 (cur-λ (n : Nat) (cur-new-elim n (cur-λ (x : Nat) Nat)
                                               (z (cur-λ (n : Nat) (cur-λ (IH : Nat) n))))))
(cur-axiom Kittens : (cur-Type 0))
(cur-axiom puppies : (Maybe Nat))
(begin-for-syntax
  (chk
   #:t (cur-normalize #'(cur-Π (B : (cur-Type 0)) (Maybe B))) ;ok
   #:t (cur-expand (cur-type-infer #'none))
   #:eq cur-equal? (cur-type-infer #'none) #'(cur-Π (A : (cur-Type 0)) (Maybe A))
   #:t (cur-normalize (cur-type-infer #'make-pair))
   #:t (cur-normalize (cur-type-infer #'empty))
   #:eq cur-equal? (cur-normalize #'(cur-Π (X : (cur-Type 0)) (Maybe X))) #'(cur-Π (X : (cur-Type 0)) (Maybe X))
   #:t (cur-normalize #'(Maybe Bool))
   #:eq cur-equal? (cur-type-infer #'cons) #'(cur-Π (A : (cur-Type 0)) (cur-Π (k : Nat) (cur-Π (x : A) (cur-Π (xs : (Vec A k)) (Vec A (s k)))))))
  (chk
   #:eq cur-equal? (cur-type-infer #'(cur-Type 0)) #'(cur-Type 1)
   #:eq cur-equal? (cur-type-infer #'(cur-λ (x : (cur-Type 0)) x)) #'(cur-Π (x : (cur-Type 0)) (cur-Type 0))
   #:eq cur-equal? (cur-type-infer #'(cur-λ (x : (cur-Π (x : (cur-Type 0)) (cur-Type 0))) x)) #'(cur-Π (x : (cur-Π (x : (cur-Type 0)) (cur-Type 0))) (cur-Π (x : (cur-Type 0)) (cur-Type 0)))
   #:x (cur-type-infer #'a) "a: unbound"
   #:eq cur-equal? (cur-type-infer #'(cur-app (cur-λ (x : (cur-Type 1)) x) (cur-Type 0))) #'(cur-Type 1)
   #:eq cur-equal? (cur-type-infer #'z) #'Nat
   #:eq cur-equal? (cur-type-infer #'s) #'(cur-Π (x : Nat) Nat)
   #:eq cur-equal? (cur-type-infer #'none) #'(cur-Π (A : (cur-Type 0)) (Maybe A))
   #:eq cur-equal? (cur-type-infer #'just) #'(cur-Π (A : (cur-Type 0)) (cur-Π (a : A) (Maybe A)))
   #:eq cur-equal? (cur-type-infer #'Kittens) #'(cur-Type 0)
   #:eq cur-equal? (cur-type-infer #'empty) #'(cur-Π (A : (cur-Type 0)) (Vec A z))
   #:eq cur-equal? (cur-type-infer #'cons) #'(cur-Π (A : (cur-Type 0)) (cur-Π (k : Nat) (cur-Π (x : A) (cur-Π (xs : (Vec A k)) (Vec A (s k))))))
 ;  #:eq cur-equal? (cur-type-infer #'(cur-app empty Bool)) #'(Vec Bool z) ;fails, returns (Vec A z))
  ; #:eq cur-equal? (cur-type-infer #'(cur-app just Nat)) #'(cur-Π (a : Nat) (Maybe Nat)) ;fails, returns (cur-Π (a : Nat) (Maybe A))
;   #:eq cur-equal? (cur-type-infer #'(cur-app none Nat)) #'(Maybe Nat) ;fails, returns (Maybe A);
   #:eq cur-equal? (cur-type-infer #'sub1) #'(cur-Π (n : Nat) Nat)
   #:eq cur-equal? (cur-type-infer #'puppies) #'(Maybe Nat))
  (chk
   #:t (cur-type-check? #'(cur-λ (x : (cur-Type 0)) x)  #'(cur-Π (x : (cur-Type 0)) (cur-Type 0)))
   #:t (cur-type-check? #'(cur-Type 0) #'(cur-Type 1))
   #:t (cur-type-check? #'z #'Nat)
   #:t (cur-type-check? #'s #'(cur-Π (x : Nat) Nat))
   #:t (cur-type-check? #'Kittens #'(cur-Type 0))
   #:t (cur-type-check? #'none #'(cur-Π (A : (cur-Type 0)) (Maybe A)))
   #:t (cur-type-check? #'(Maybe Nat) #'(cur-Type 0))
  ; #:t (cur-type-check? #'Maybe  #'(cur-Π (A : (cur-Type 0)) (cur-Type 0))) ;fails: bad syntax in Maybe. Datatypes are defined with all params and indices in dep-ind-cur
   #:t (cur-type-check? #'Nat #'(cur-Type 0))
   #:t (cur-type-check? #'just #'(cur-Π (A : (cur-Type 0)) (cur-Π (a : A) (Maybe A)))))
  (chk
  #:= (cur->datum #'(cur-Type 0)) '(cur-Type 0)
  #:= (cur->datum #'(cur-λ (a : (cur-Type 0)) a)) '(cur-λ (a : (cur-Type 0)) a)
  #:= (cur->datum #'(cur-Π (a : (cur-Type 0)) (cur-Type 0))) '(cur-Π (a : (cur-Type 0)) (cur-Type 0))
  ;#:= (cur->datum #'(cur-app (cur-λ (x : (cur-Type 1)) x) (cur-Type 0))) '(cur-app (cur-λ (x : (cur-Type 1)) x) (cur-Type 0)) ;fails bc evaluation
  #:= (cur->datum #'(cur-app s z)) '(cur-app s z)
  #:= (cur->datum #'(cur-app s (cur-app s z))) '(cur-app s (cur-app s z))
  #:= (cur->datum #'(cur-app just Nat)) '(cur-app just Nat)
  #:= (cur->datum #'(cur-app sub1 z)) '(cur-app sub1 z)
  #:= (cur->datum #'Kittens) 'Kittens
 #;#; #:= (cur->datum #'(cur-new-elim False (cur-λ (x : Bool) Nat) ((s z) z))) '(cur-new-elim False (cur-λ (x : Bool) Nat) ((s z) z))) ;fails bc evaluation
 (chk
  #:eq cur-equal? (cur-normalize #'(cur-Type 1)) #'(cur-Type 1)
  #:eq cur-equal? (cur-normalize #'(cur-λ (x : (cur-Type 0)) x)) #'(cur-λ (x : (cur-Type 0)) x)
  #:eq cur-equal? (cur-normalize #'(cur-app (cur-λ (x : (cur-Type 1)) x) (cur-Type 0))) #'(cur-Type 0)
  #:eq cur-equal? (cur-normalize #'(((cur-λ (A : (cur-Type 3)) (cur-λ (a : (cur-Type 2)) a)) (cur-Type 2)) (cur-Type 1))) #'(cur-Type 1)
  #:eq cur-equal? (cur-normalize #'(cur-app s z)) #'(cur-app s z)
  #;#;#;#:eq cur-equal? (cur-normalize #'(cur-app sub1 (cur-app s z))) #'z) ;fails,doesn't apply sub1, returns (cur-app sub1 (cur-app s z))
  #;(chk ;not equal by =
 #:eq cur-equal? (cur-constructors-for #'Nat) (list #'s #'z)
 #:eq cur-equal? (cur-constructors-for #'(Maybe Bool)) (list #'none #'just))
#;(chk ;substitutes the bound var
 #:= (cur-rename #'Y #'X #'((cur-λ (X : (cur-Type 0)) X) X)) #'((cur-λ (X : (Type 0)) X) Y))
(chk ;Note: can't test (cur-data-parameters #'Maybe) (see above)
 #:= (cur-data-parameters #'Nat) 0
 #:= (cur-data-parameters #'(Maybe Bool)) 1)
(chk
 #:= (cur-constructor-telescope-length #'z) 0
 #:= (cur-constructor-telescope-length #'s) 1
 #:= (cur-constructor-telescope-length #'cons) 4
 #:= (cur-constructor-telescope-length #'empty) 1
 #:= (cur-constructor-recursive-index-ls #'z) '()
 #:= (cur-constructor-recursive-index-ls #'s) '(0)
 #:= (cur-constructor-recursive-index-ls #'make-pair) '()
 #:= (cur-constructor-recursive-index-ls #'cons) '(3))
;(displayln (cur-type-infer #'none))
;(displayln (cur->datum (cur-type-infer #'none)))
)
