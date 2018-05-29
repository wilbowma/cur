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

(turn-data Nat : 0 (turn-Type 0)
           (z :   Nat)
           (s : (turn-Π (x : Nat) Nat)))
(turn-data Maybe : 1 (turn-Π (A : (turn-Type 0)) (turn-Type 0))
           (none : (turn-Π (A : (turn-Type 0)) (Maybe A)))
           (just : (turn-Π (A : (turn-Type 0)) (turn-Π (a : A) (Maybe A)))))
(turn-data Vec : 1 (turn-Π (A : (turn-Type 0)) (turn-Π (n : Nat) (turn-Type 0)))
           (empty : (turn-Π (A : (turn-Type 0)) (Vec A z)))
           (cons : (turn-Π (A : (turn-Type 0))
                           (turn-Π (k : Nat)
                                   (turn-Π (x : A) (turn-Π (xs : (Vec A k))
                                                           (Vec A (s k))))))))
(turn-data Pair : 2 (turn-Π (A : (turn-Type 0)) (turn-Π (B : (turn-Type 0)) (turn-Type 0)))
           (make-pair : (turn-Π (A : (turn-Type 0)) (turn-Π (B : (turn-Type 0)) (Pair A B)))))
(turn-data Bool : 0 (turn-Type 0)
           (True : Bool)
           (False : Bool))
(define sub1 (turn-λ (n : Nat) (turn-new-elim n (turn-λ (x : Nat) Nat)
                                               (z (turn-λ (n : Nat) (turn-λ (IH : Nat) n))))))
(turn-axiom Kittens : (turn-Type 0))
(turn-axiom puppies : (Maybe Nat))
(begin-for-syntax
#;  (displayln (format "turnstile-only infer type of empty: ~a\n\n" (syntax->datum  (car (cadddr (infer (list #'empty )))))))
#;  (displayln (format "turnstile-only evaluated infer type of empty: ~a\n\n" (syntax->datum  (cur-eval (car (cadddr (infer (list #'empty ))))))))
  (chk
   #:t (cur-normalize #'(turn-Π (B : (turn-Type 0)) (Maybe B))) ;ok
   #:t (cur-eval (cur-type-infer #'none))
   #:eq cur-equal? (cur-type-infer #'none) #'(turn-Π (A : (turn-Type 0)) (Maybe A))
   #:t (cur-normalize (cur-type-infer #'make-pair))
   #:t (cur-normalize (cur-type-infer #'empty))
   #:eq cur-equal? (cur-normalize #'(turn-Π (X : (turn-Type 0)) (Maybe X))) #'(turn-Π (X : (turn-Type 0)) (Maybe X))
   #:t (cur-normalize #'(Maybe Bool))
   #:eq cur-equal? (cur-type-infer #'cons) #'(turn-Π (A : (turn-Type 0)) (turn-Π (k : Nat) (turn-Π (x : A) (turn-Π (xs : (Vec A k)) (Vec A (s k)))))))
  (chk
   #:eq cur-equal? (cur-type-infer #'(turn-Type 0)) #'(turn-Type 1)
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-Π (x : (turn-Type 0)) (turn-Type 0))
   #:eq cur-equal? (cur-type-infer #'(turn-λ (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) x)) #'(turn-Π (x : (turn-Π (x : (turn-Type 0)) (turn-Type 0))) (turn-Π (x : (turn-Type 0)) (turn-Type 0)))
   #:x (cur-type-infer #'a) "a: unbound"
   #:eq cur-equal? (cur-type-infer #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 1)
   #:eq cur-equal? (cur-type-infer #'z) #'Nat
   #:eq cur-equal? (cur-type-infer #'s) #'(turn-Π (x : Nat) Nat)
   #:eq cur-equal? (cur-type-infer #'none) #'(turn-Π (A : (turn-Type 0)) (Maybe A))
   #:eq cur-equal? (cur-type-infer #'just) #'(turn-Π (A : (turn-Type 0)) (turn-Π (a : A) (Maybe A)))
   #:eq cur-equal? (cur-type-infer #'Kittens) #'(turn-Type 0)
   #:eq cur-equal? (cur-type-infer #'empty) #'(turn-Π (A : (turn-Type 0)) (Vec A z))
   #:eq cur-equal? (cur-type-infer #'cons) #'(turn-Π (A : (turn-Type 0)) (turn-Π (k : Nat) (turn-Π (x : A) (turn-Π (xs : (Vec A k)) (Vec A (s k))))))
 ;  #:eq cur-equal? (cur-type-infer #'(turn-app empty Bool)) #'(Vec Bool z) ;fails, returns (Vec A z))
  ; #:eq cur-equal? (cur-type-infer #'(turn-app just Nat)) #'(turn-Π (a : Nat) (Maybe Nat)) ;fails, returns (turn-Π (a : Nat) (Maybe A))
;   #:eq cur-equal? (cur-type-infer #'(turn-app none Nat)) #'(Maybe Nat) ;fails, returns (Maybe A);
   #:eq cur-equal? (cur-type-infer #'sub1) #'(turn-Π (n : Nat) Nat)
   #:eq cur-equal? (cur-type-infer #'puppies) #'(Maybe Nat))
  (chk
   #:t (cur-type-check? #'(turn-λ (x : (turn-Type 0)) x)  #'(turn-Π (x : (turn-Type 0)) (turn-Type 0)))
   #:t (cur-type-check? #'(turn-Type 0) #'(turn-Type 1))
   #:t (cur-type-check? #'z #'Nat)
   #:t (cur-type-check? #'s #'(turn-Π (x : Nat) Nat))
   #:t (cur-type-check? #'Kittens #'(turn-Type 0))
   #:t (cur-type-check? #'none #'(turn-Π (A : (turn-Type 0)) (Maybe A)))
   #:t (cur-type-check? #'(Maybe Nat) #'(turn-Type 0))
  ; #:t (cur-type-check? #'Maybe  #'(turn-Π (A : (turn-Type 0)) (turn-Type 0))) ;fails: bad syntax in Maybe. Datatypes are defined with all params and indices in dep-ind-cur
   #:t (cur-type-check? #'Nat #'(turn-Type 0))
   #:t (cur-type-check? #'just #'(turn-Π (A : (turn-Type 0)) (turn-Π (a : A) (Maybe A)))))
  (chk
  #:= (cur->datum #'(turn-Type 0)) '(turn-Type 0)
  #:= (cur->datum #'(turn-λ (a : (turn-Type 0)) a)) '(turn-λ (a : (turn-Type 0)) a)
  #:= (cur->datum #'(turn-Π (a : (turn-Type 0)) (turn-Type 0))) '(turn-Π (a : (turn-Type 0)) (turn-Type 0))
  ;#:= (cur->datum #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) '(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0)) ;fails bc evaluation
  #:= (cur->datum #'(turn-app s z)) '(turn-app s z)
  #:= (cur->datum #'(turn-app s (turn-app s z))) '(turn-app s (turn-app s z))
  #:= (cur->datum #'(turn-app just Nat)) '(turn-app just Nat)
  #:= (cur->datum #'(turn-app sub1 z)) '(turn-app sub1 z)
  #:= (cur->datum #'Kittens) 'Kittens
 #;#; #:= (cur->datum #'(turn-new-elim False (turn-λ (x : Bool) Nat) ((s z) z))) '(turn-new-elim False (turn-λ (x : Bool) Nat) ((s z) z))) ;fails bc evaluation
 (chk
  #:eq cur-equal? (cur-normalize #'(turn-Type 1)) #'(turn-Type 1)
  #:eq cur-equal? (cur-normalize #'(turn-λ (x : (turn-Type 0)) x)) #'(turn-λ (x : (turn-Type 0)) x)
  #:eq cur-equal? (cur-normalize #'(turn-app (turn-λ (x : (turn-Type 1)) x) (turn-Type 0))) #'(turn-Type 0)
  #:eq cur-equal? (cur-normalize #'(((turn-λ (A : (turn-Type 3)) (turn-λ (a : (turn-Type 2)) a)) (turn-Type 2)) (turn-Type 1))) #'(turn-Type 1)
  #:eq cur-equal? (cur-normalize #'(turn-app s z)) #'(turn-app s z)
  #;#;#;#:eq cur-equal? (cur-normalize #'(turn-app sub1 (turn-app s z))) #'z) ;fails,doesn't apply sub1, returns (turn-app sub1 (turn-app s z))
  #;(chk ;not equal by =
 #:eq cur-equal? (cur-constructors-for #'Nat) (list #'s #'z)
 #:eq cur-equal? (cur-constructors-for #'(Maybe Bool)) (list #'none #'just))
#;(chk ;substitutes the bound var
 #:= (cur-rename #'Y #'X #'((turn-λ (X : (turn-Type 0)) X) X)) #'((turn-λ (X : (Type 0)) X) Y))
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
