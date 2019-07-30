#lang cur

(require cur/stdlib/sugar
         rackunit/turnstile)

(typecheck-fail/toplvl
 (define-datatype Inf : (-> Type Type)
   (Delay : (forall (A : Type) (-> A Inf A))))
 #:with-msg "expected \\(Type n\\) \\(for some n\\), given \\(→ \\(Type 0\\) \\(Type 0\\)\\)")

; #2
#;(define-datatype Inf : (-> Type Type)
  (Delay : (forall (A : Type) (-> A (Inf A)))))

; #3
#;(define-datatype Inf (A : Type) : Type
  (Delay : (-> A (Inf A))))

(define-datatype Inf (A : Type) : Type
  (Delay A))

; #4
#;(define/rec/match Force : (Inf A) -> A
  [(Delay x) x])

; #5
(define/rec/match Force : [A : Type] (Inf A) -> A
  [(Delay _ x) => x])
