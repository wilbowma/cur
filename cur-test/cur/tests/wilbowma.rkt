#lang cur

(require cur/stdlib/sugar
         rackunit/turnstile)

(typecheck-fail/toplvl
 (define-datatype Inf : (-> Type Type)
   (Delay : (forall (A : Type) (-> A Inf A))))
 #:with-msg "type mismatch: Inf has type \\(-> \\(Type 0\\) \\(Type 0\\)\\), expected Type")

; #2
#;(define-datatype Inf : (-> Type Type)
  (Delay : (forall (A : Type) (-> A (Inf A)))))

; #3
#;(define-datatype Inf (A : Type) : Type
  (Delay : (-> A (Inf A))))

(define-datatype Inf (A : Type) : -> Type
  (Delay : [a : A] -> (Inf A)))

; #4
#;(define/rec/match Force : (Inf A) -> A
  [(Delay x) x])

; #5
(define/rec/match Force : [A : Type] (Inf A) -> A
  [(Delay _ x) => x])
