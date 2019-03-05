#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/stdlib/prop
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

; Software Foundations Logic.v

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

(define/rec/match plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (plus n-1 m))])

(define/rec/match pred : nat -> nat
  [O => O]
  [(S n-1) => n-1])

;(define-theorem and-intro ; TODO: add split tactic
;(define-theorem and-example1 

(define-theorem and-example2
  (∀ [n m : nat] (-> (And (== n 0) (== m 0))
                     (== (plus n m) 0)))
  (by-intros n m H)
  (by-destruct H #:as [(Hn Hm)])
  (by-rewrite Hn)
  (by-rewrite Hm)
  reflexivity)

(define-theorem ex-falso-quodlibet
  (forall (P : Prop) (-> False P))
  (by-intros P contra)
  (by-destruct contra))

(define-theorem function-equality1
  (== (plus 3) (plus (pred 4)))
  reflexivity)

;; needs functional extensionality axiom
#;(define-theorem function-equality2
  (== (λ [x : nat] (plus x 1))
      (λ [x : nat] (plus 1 x)))
  #;stuck)

;; TODO: add define-axiom


