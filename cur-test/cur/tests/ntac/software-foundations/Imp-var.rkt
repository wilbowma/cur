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

;; nb: this file may take a few min to run

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
 
(define-theorem ceval-deterministic
  (∀ [c : com] [st : State] [st1 : State] [st2 : State]
     (-> (ceval c st st1)
         (ceval c st st2)
         (== State st1 st2)))
  (by-intros c st st1 st2 E1 E2)
  ;; TODO: fixme: this will be shadowed (by induction E1 with no params) if it's st2
  (by-generalize st2)
  (by-induction E1 #:as [(st) ; skip
                         (st a1 n x E) ; ass
                         (c10 c20 st0 st10 st20 E10 E20 IH10 IH20) ; seq
                         (st st1 b c1 c2 bE E IH) ; iftrue
                         (st st1 b c1 c2 bE E IH) ; iffalse
                         (b st c bE) ; whilefalse
                         (st0 st10 st20 b c bE E1 E2 IH1 IH2)]) ; whiletrue
  ; 1 ESkip
  (by-intros st2b E2b)
  (by-inversion E2b #:as st0 H0 H1)
;  subst ; TODO: use subst instead of explicit rewrites
  (by-rewriteL H0)
  (by-rewriteL H1)
  reflexivity
  ; 2 EAss
  (by-intros st2b E2b)
  (by-inversion E2b #:as st0 a0 n0 x0 H0 H1 H2 H3 H4)
  (by-rewriteL E)
  (by-rewriteL H1)
  (by-rewriteL H0)
  (by-rewriteL H2)
  (by-rewriteL H3)
  (by-rewriteL H4)
  reflexivity
  ; 3 ESeq
  (by-intros st2b E2b)
  ;subst
  (by-inversion E2b #:as c11 c21 st1 st11 st21 E11 E21 H0 H1 H2 H3)
  (by-assert EQ1 (== st10 st11))
  (by-apply IH10) ; EQ1
  (by-rewriteL H1)
  (by-rewriteL H3)
  by-assumption ; end EQ1
  (by-apply IH20)
  (by-rewriteL H0)
  (by-rewriteL H2)
  (by-rewrite EQ1)
  by-assumption
  ;; 4 EIfTrue
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)
                          (st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)])
  ;; 4a
  (by-apply IH)
  (by-rewriteL H0)
  (by-rewriteL H1)
  (by-rewriteL H3)
  by-assumption
  ;; 4b
  (by-rewriteL H1 #:in bE)
  (by-rewriteL H4 #:in bE)
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 5 EIfFalse
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)
                          (st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)])
  ;; 5a
  (by-rewriteL H1 #:in bE)
  (by-rewriteL H4 #:in bE)
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 5b
  (by-apply IH)
  (by-rewriteL H0)
  (by-rewriteL H1)
  (by-rewriteL H2)
  by-assumption
  ;; 6 EWhileFalse
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(b0 st0 c0 bE0 H0 H1 H2 H3)
                          (st0 st1 st2 b0 c0 bE0 H0 H1 H2 H3 H4 H5)])
  ;; 6a
  (by-rewriteL H0)
  (by-rewriteL H1)
  reflexivity
  ;; 6b
  (by-rewriteL H3 #:in bE)
  (by-rewriteL H5 #:in bE)
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 7 EWhileTrue
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(b0 st1 c0 bE0 H0 H1 H2 H3)
                          (st1 st11 st21 b0 c0 bE0 E10 E20 H0 H1 H2 H3)])
  ;; 7a
  (by-rewriteL H1 #:in bE)
  (by-rewriteL H3 #:in bE)
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 7b
  (by-assert EQ1 (== st10 st11))
  (by-apply IH1) ; EQ1
  (by-rewriteL H1)
  (by-rewriteL H2)
  by-assumption ; end EQ1
  (by-apply IH2)
  (by-rewrite EQ1)
  (by-rewriteL H0)
  (by-rewriteL H2)
  (by-rewriteL H3)
  by-assumption)

;; dont run to save time
#;(define-theorem ceval-deterministic/subst
  (∀ [c : com] [st : State] [st1 : State] [st2 : State]
     (-> (ceval c st st1)
         (ceval c st st2)
         (== State st1 st2)))
  (by-intros c st st1 st2 E1 E2)
  ;; TODO: fixme: this will be shadowed (by induction E1 with no params) if it's st2
  (by-generalize st2)
  (by-induction E1 #:as [(st) ; skip
                         (st a1 n x E) ; ass
                         (c10 c20 st0 st10 st20 E10 E20 IH10 IH20) ; seq
                         (st st1 b c1 c2 bE E IH) ; iftrue
                         (st st1 b c1 c2 bE E IH) ; iffalse
                         (b st c bE) ; whilefalse
                         (st0 st10 st20 b c bE E1 E2 IH1 IH2)]) ; whiletrue
  ; 1 ESkip
  (by-intros st2b E2b)
  (by-inversion E2b #:as st0 H0 H1)
  subst
  reflexivity
  ; 2 EAss
  (by-intros st2b E2b)
  (by-inversion E2b #:as st0 a0 n0 x0 H0 H1 H2 H3 H4)
  subst
  reflexivity
  ; 3 ESeq
  (by-intros st2b E2b)
  (by-inversion E2b #:as c11 c21 st1 st11 st21 E11 E21 H0 H1 H2 H3)
  subst
  (by-assert EQ1 (== st10 st11))
  (by-apply IH10) ; EQ1
  by-assumption ; end EQ1
  (by-apply IH20)
  (by-rewrite EQ1)
  by-assumption
  ;; 4 EIfTrue
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)
                          (st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)])
  ;; 4a
  subst
  (by-apply IH)
  by-assumption
  ;; 4b
  subst
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 5 EIfFalse
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)
                          (st0 st10 b0 c10 c20 bE0 E0 H0 H1 H2 H3 H4)])
  ;; 5a
  subst
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 5b
  subst
  (by-apply IH)
  by-assumption
  ;; 6 EWhileFalse
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(b0 st0 c0 bE0 H0 H1 H2 H3)
                          (st0 st1 st2 b0 c0 bE0 H0 H1 H2 H3 H4 H5)])
  ;; 6a
  subst
  reflexivity
  ;; 6b
  subst
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 7 EWhileTrue
  (by-intros st2b E2b)
  (by-inversion E2b #:as [(b0 st1 c0 bE0 H0 H1 H2 H3)
                          (st1 st11 st21 b0 c0 bE0 E10 E20 H0 H1 H2 H3)])
  ;; 7a
  subst
  (by-rewrite bE #:in bE0)
  (by-discriminate bE0)
  ;; 7b
  subst
  (by-assert EQ1 (== st10 st11))
  (by-apply IH1) ; EQ1
  by-assumption ; end EQ1
  (by-apply IH2)
  (by-rewrite EQ1)
  by-assumption)

(define-theorem ceval-deterministic/subst/seq
;(ntac/trace
  (∀ [c : com] [st : State] [st1 : State] [st2 : State]
     (-> (ceval c st st1)
         (ceval c st st2)
         (== State st1 st2)))
  (by-intros c st st1 st2 E1 E2)
  ;; TODO: fixme: this will be shadowed (by induction E1 with no params) if it's st2
  (by-generalize st2)
  (seq
   (by-induction E1 #:as [(st0) ; skip
                          (st0 a n x E) ; ass
                          (c1 c2 st0 st10 st20 E10 E20 IH1 IH2) ; seq
                          (st0 st10 b c1 c2 bE E IH) ; iftrue
                          (st0 st10 b c1 c2 bE E IH) ; iffalse
                          (b st0 c0 bE) ; whilefalse
                          (st0 st10 st20 b c bE E10 E20 IH1 IH2)]) ; whiletrue
   (by-intros st2b E2b)
   ;; not specifying explicit names here works fine;
   ;; but specifying these (somewhat unintuitive) names helps code maintenance
   (by-inversion E2b #:as [(c11 c22/st11 st01 st11/bE0 st21) ; case 3
                           (bE0 E0 H0 H1 H2/st11 H3 H4)
                           (st02 st12/bE1 b0 c12 c22 bE1)]) ; case 4b, 5a, 6b
   subst)
  ; 1 ESkip
  reflexivity
  ; 2 EAss
  reflexivity
  ; 3 ESeq
  (by-assert EQ1 (== st10 st11/bE0))
  (by-apply IH1) ; EQ1
  by-assumption  ; end EQ1
  (by-apply IH2)
  (by-rewrite EQ1)
  by-assumption
  ;; 4 EIfTrue
  (by-apply IH)                 ; 4a
  by-assumption
  (by-rewrite bE #:in bE1) ; 4b
  (by-discriminate bE1)
  ;; 5 EIfFalse
  (by-rewrite bE #:in bE0) ; 5a
  (by-discriminate bE0)
  (by-apply IH)                 ; 5b
  by-assumption
  ;; 6 EWhileFalse
  reflexivity                   ; 6a
  (by-rewrite bE #:in st12/bE1) ; 6b
  (by-discriminate st12/bE1)
  ;; 7 EWhileTrue
  (by-rewrite bE #:in st11/bE0)     ; 7a
  (by-discriminate st11/bE0)
  (by-assert EQ1 (== st10 H2/st11)) ; 7b
  (by-apply IH1) ; EQ1
  by-assumption  ; end EQ1
  (by-apply IH2)
  (by-rewrite EQ1)
  by-assumption)

(check-type ceval-deterministic
  : (∀ [c : com] [st : State] [st1 : State] [st2 : State]
     (-> (ceval c st st1)
         (ceval c st st2)
         (== State st1 st2))))

#;(check-type ceval-deterministic/subst
  : (∀ [c : com] [st : State] [st1 : State] [st2 : State]
     (-> (ceval c st st1)
         (ceval c st st2)
         (== State st1 st2))))

(check-type ceval-deterministic/subst/seq
  : (∀ [c : com] [st : State] [st1 : State] [st2 : State]
     (-> (ceval c st st1)
         (ceval c st st2)
         (== State st1 st2))))
