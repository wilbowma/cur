#lang cur

(require
 cur/stdlib/datum
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/ascii
 cur/stdlib/sugar
 cur/stdlib/equality
 cur/ntac/base
 cur/ntac/standard
 cur/ntac/rewrite
 rackunit/turnstile
 "../rackunit-ntac.rkt")

(define (total-map [A : Type]) (-> String A))
(define (update_ [A : Type] [m : (total-map A)] [x : String] [v : A])
  (λ [y : String] (if (string-equal? x y) v (m y))))
(define-implicit update = update_ 1)

(define State (total-map Nat))

(define-datatype aexp : Type
  [ANum (n : Nat)]
  [AId (x : String)]
  [APlus (a1 a2 : aexp)]
  [AMinus (a1 a2 : aexp)]
  [AMult (a1 a2 : aexp)])

(define W "W")
(define X "X")
(define Y "Y")
(define Z "Z")

(define-datatype bexp : Type
  [BTrue]
  [BFalse]
  [BEq (a1 a2 : aexp)]
  [BLe (a1 a2 : aexp)]
  [BNot (b : bexp)]
  [BAnd (b1 b2 : bexp)])

(define/rec/match aeval : [st : State] aexp -> Nat
  [(ANum n) => n]
  [(AId x) => (st x)]
  [(APlus  a1 a2) => (plus (aeval st a1) (aeval st a2))]
  [(AMinus a1 a2) => (minus (aeval st a1) (aeval st a2))]
  [(AMult  a1 a2) => (mult (aeval st a1) (aeval st a2))])

(define empty-st (λ [x : String] 0))

(define-theorem test_aeval1
  (== (aeval empty-st (APlus (ANum 2) (ANum 2))) 4)
  reflexivity)

(define/rec/match beval : [st : State] bexp -> Bool
  [BTrue       => true]
  [BFalse      => false]
  [(BEq a1 a2)   => (nat-equal? (aeval st a1) (aeval st a2))]
  [(BLe a1 a2)   => (<= (aeval st a1) (aeval st a2))]
  [(BNot b1)     => (not (beval st b1))]
  [(BAnd b1 b2)  => (and (beval st b1) (beval st b2))])

(define (bool-to-bexp [b : Bool])
  (if b BTrue BFalse))

(define aexp-example1
  (aeval (update empty-st X 5) (APlus (ANum 3) (AMult (AId X) (ANum 2)))))
(check-type aexp-example1 : Nat -> 13)

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(begin-for-syntax
  (current-datum
   (λ (syn f)
     (syntax-parse/typecheck syn
      [x:nat ⇐ ~aexp ≫
       ----------------
       [⊢ (ANum x)]]
      [s:str ⇐ ~aexp ≫
       ----------------
       [⊢ (AId s)]]
      [b:boolean ⇐ ~bexp ≫
       ----------------
       [⊢ (bool-to-bexp #,(if (syntax-e #'b) #'true #'false))]]
      [_ ≫ --- [≻ #,(f syn)]]))))
 
(define aexp-example/new-datum
  (aeval (update empty-st "X" 5) (APlus 3 (AMult "X" 2))))
(define-theorem aexp/new-datum
  (== 13 aexp-example/new-datum)
  reflexivity)

(define bexp-example
  (beval (update empty-st X 5) (BAnd #t (BNot (BLe "X" 4)))))
(define-theorem bexp1
  (== true bexp-example)
  reflexivity)

(define-datatype com : Type
  [CSkip]
  [CAss (x : String) (a : aexp)]
  [CSeq (c1 c2 : com)]
  [CIf (b : bexp) (c1 c2 : com)]
  [CWhile (b : bexp) (c : com)])

(define-syntax CSeqs
  (syntax-parser
    [(_ x) #'x]
    [(_ x y) #'(CSeq x y)]
    [(_ x . rst) #'(CSeq x (CSeqs . rst))]))

(define-typed-variable-syntax
  [(_ _ ≫ x- : ~String) ⇐ ~aexp ≫
   ----------
   [⊢ (AId x-)]]
  [(_ _ ≫ x- : σ) ≫
   ----------
   [⊢ x- ⇒ σ]])

(define fact-in-cur
  (CSeqs (CAss Z X)
         (CAss Y 1)
         (CWhile (BNot (BEq Z 0))
                 (CSeq (CAss Y (AMult Y Z))
                       (CAss Z (AMinus Z 1))))))

(check-type fact-in-cur : com)

;; ceval must be relation, bc fn wouldnt terminate
(define-datatype ceval : (-> com State State Prop)
  [ESkip : (∀ [st : State] (ceval CSkip st st))]
  [EAss  : (∀ [st : State] [a1 : aexp] [n : Nat] [x : String]
              (-> (== (aeval st a1) n)
                  (ceval (CAss x a1) st (update st x n))))]
  [ESeq  : (∀ [c1 c2 : com] [st st1 st2 : State]
              (-> (ceval c1 st st1)
                  (ceval c2 st1 st2)
                  (ceval (CSeq c1 c2) st st2)))]
  [EIfTrue  : (∀ [st st1 : State] [b : bexp] [c1 c2 : com]
                 (-> (== (beval st b) true)
                     (ceval c1 st st1)
                     (ceval (CIf b c1 c2) st st1)))]
  [EIfFalse : (∀ [st st1 : State] [b : bexp] [c1 c2 : com]
                 (-> (== (beval st b) false)
                     (ceval c2 st st1)
                     (ceval (CIf b c1 c2) st st1)))]
  [EWhileFalse : (∀ [b : bexp] [st : State] [c : com]
                    (-> (== (beval st b) false)
                        (ceval (CWhile b c) st st)))]
  [EWhileTrue  : (∀ [st st1 st2 : State] [b : bexp] [c : com]
                    (-> (== (beval st b) true)
                        (ceval c st st1)
                        (ceval (CWhile b c) st1 st2)
                        (ceval (CWhile b c) st st2)))])

(define-theorem eval-example1
  (ceval (CSeq (CAss "X" 2)
               (CIf (BLe "X" 1)
                    (CAss "Y" 3)
                    (CAss "Z" 4)))
         empty-st
         (update (update empty-st "X" 2) "Z" 4))
  (by-apply ESeq #:with-var [st1 (update empty-st "X" 2)])
  ;; TODO: improve unification (fold results) so #:with-var not necessary
  (by-apply EAss #:with-var [st empty-st]) ; 1
  reflexivity
  (by-apply EIfFalse) ; 2
  reflexivity
  (by-apply EAss #:with-var [st (update empty-st "X" 2)])
  reflexivity)
