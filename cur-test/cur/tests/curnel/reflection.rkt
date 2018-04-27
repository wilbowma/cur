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
(turn-data Vec : 1 (turn-Π (A : (turn-Type 0)) (turn-Π (n : Nat2) (turn-Type 0)))
           (empty : (turn-Π (A : (turn-Type 0)) (Vec A z2)))
           (cons : (turn-Π (A : (turn-Type 0))
                           (turn-Π (k : Nat2)
                                   (turn-Π (x : A) (turn-Π (xs : (Vec A k))
                                                           (Vec A (s2 k))))))))
(turn-data Bool : 0 (turn-Type 0)
           (True : Bool)
           (False : Bool))
(define sub1 (turn-λ (n : Nat2) (turn-new-elim n (turn-λ (x : Nat2) Nat2)
                                               (z2 (turn-λ (n : Nat2) (turn-λ (IH : Nat2) n))))))
(turn-axiom Kittens : (turn-Type 0))
(turn-axiom puppies : (Maybe Nat2))
(begin-for-syntax 
  (chk 
   #:t (cur-equal? #'(turn-λ (x : (turn-Type 0)) x) #'(turn-λ (x : (turn-Type 0)) x) )
   #:t (cur-equal? #'(turn-Type 0) #'(turn-Type 0))
   #:t (cur-equal? #'(turn-Π (x : (turn-Type 0)) (turn-Type 0)) #'(turn-Π (x : (turn-Type 0)) (turn-Type 0)))
   #:t (cur-equal? #'(Maybe Bool) #'(Maybe Bool)))
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
   #:eq cur-equal? (cur-type-infer #'empty) #'(turn-Π (A : (turn-Type 0)) (Vec A z2))
   #:eq cur-equal? (cur-type-infer #'cons) #'(turn-Π (A : (turn-Type 0)) (turn-Π (k : Nat2) (turn-Π (x : A) (turn-Π (xs : (Vec A k)) (Vec A (s2 k))))))
  ;; #:eq cur-equal? (cur-type-infer #'(turn-app empty Bool)) #'(Vec Bool z2) ;fails, returns (Vec A z2))
  ;; #:eq cur-equal? (cur-type-infer #'(turn-app just Nat2)) #'(turn-Π (a : Nat2) (Maybe Nat2)) ;fails, returns (turn-Π (a : Nat2) (Maybe A))
  ;; #:eq cur-equal? (cur-type-infer #'(turn-app none Nat2)) #'(Maybe Nat2) ;fails, returns (Maybe A);
   #:eq cur-equal? (cur-type-infer #'sub1) #'(turn-Π (n : Nat2) Nat2)
   #:eq cur-equal? (cur-type-infer #'puppies) #'(Maybe Nat2))
  (chk
   #:t (cur-type-check? #'(turn-λ (x : (turn-Type 0)) x)  #'(turn-Π (x : (turn-Type 0)) (turn-Type 0))) 
   #:t (cur-type-check? #'(turn-Type 0) #'(turn-Type 1))
   #:t (cur-type-check? #'z2 #'Nat2)
   #:t (cur-type-check? #'s2 #'(turn-Π (x : Nat2) Nat2))
   #:t (cur-type-check? #'Kittens #'(turn-Type 0))
   #:t (cur-type-check? #'none #'(turn-Π (A : (turn-Type 0)) (Maybe A)))
   #:t (cur-type-check? #'(Maybe Nat2) #'(turn-Type 0))
  ; #:t (cur-type-check? #'Maybe  #'(turn-Π (A : (turn-Type 0)) (turn-Type 0))) ;fails: bad syntax in Maybe. Datatypes are defined with all params and indices in dep-ind-cur
   #:t (cur-type-check? #'Nat2 #'(turn-Type 0))
   #:t (cur-type-check? #'just #'(turn-Π (A : (turn-Type 0)) (turn-Π (a : A) (Maybe A)))))
  (chk
  #:= (cur->datum #'(turn-Type 0)) '(turn-Type 0)
  #:= (cur->datum #'(turn-λ (a : (turn-Type 0)) a)) '(turn-λ (a : (turn-Type 0)) a) 
  #:= (cur->datum #'(turn-Π (a : (turn-Type 0)) (turn-Type 0))) '(turn-Π (a : (turn-Type 0)) (turn-Type 0))
  ;#:= (cur->datum #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) '(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0)) ;fails bc evaluation
  #:= (cur->datum #'(turn-app s2 z2)) '(turn-app s2 z2)
  #:= (cur->datum #'(turn-app s2 (turn-app s2 z2))) '(turn-app s2 (turn-app s2 z2))
  #:= (cur->datum #'(turn-app just Nat2)) '(turn-app just Nat2)
  #:= (cur->datum #'(turn-app sub1 z2)) '(turn-app sub1 z2)
  #:= (cur->datum #'Kittens) 'Kittens
 #;#; #:= (cur->datum #'(turn-new-elim False (turn-λ (x : Bool) Nat2) ((s2 z2) z2))) '(turn-new-elim False (turn-λ (x : Bool) Nat2) ((s2 z2) z2))) ;fails bc evaluation
  (chk
  #:eq cur-equal? (cur-normalize #'(turn-Type 1)) #'(turn-Type 1)
  #:eq cur-equal? (cur-normalize #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-λ (x : (turn-Type 0)) x) 
  #:eq cur-equal? (cur-normalize #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 0)
  #:eq cur-equal? (cur-normalize #'(((turn-λ (A : (turn-Type 3)) (turn-λ (a : (turn-Type 2)) a)) (turn-Type 2)) (turn-Type 1))) #'(turn-Type 1) 
  #:eq cur-equal? (cur-normalize #'(turn-app s2 z2)) #'(turn-app s2 z2)
  #;#;#;#:eq cur-equal? (cur-normalize #'(turn-app sub1 (turn-app s2 z2))) #'z2) ;fails,doesn't apply sub1, returns (turn-app sub1 (turn-app s2 z2))
#;(chk ;not equal by =
 #:= (cur-constructors-for #'Nat2) (list #'s2 #'z2)
 #:= (cur-constructors-for #'(Maybe Bool)) (list #'none #'just))
#;(chk ;substitutes the bound var
 #:= (cur-rename #'Y #'X #'((turn-λ (X : (turn-Type 0)) X) X)) #'((turn-λ (X : (Type 0)) X) Y))
(chk ;Note: can't test (cur-data-parameters #'Maybe) (see above) 
 #:= (cur-data-parameters #'Nat2) 0
 #:= (cur-data-parameters #'(Maybe Bool)) 1)) 