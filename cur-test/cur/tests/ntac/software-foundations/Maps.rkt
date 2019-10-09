#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/stdlib/bool
         cur/stdlib/ascii
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile+
         "../rackunit-ntac.rkt")

; examples from Software Foundations Maps.v

;; this can only work if, like Coq, ascii-equal? returns proof that x \neq x
;; TODO: add sumbool?
#;(define-theorem beq-string-refl
  (∀ [s : String] (== true (string-equal? s s)))
  (by-intro s)
  (by-induction s #:as [() (x xs IH)])
  reflexivity ;1
  ;  (by-destruct x #:as [(a1 a2 a3 a4 a5 a6 a7)]) ;2
  (by-destruct (ascii-equal? x x)) ;2
  by-assumption ;2a
  ; stuck proving t=f
  )

(define-theorem beq-string-refl
  (∀ [s : String] (== true (string-equal? s s)))
  (by-intro s)
  (by-induction s #:as [() (x xs IH)])
  reflexivity ;1
  (by-destruct x #:as [(a1 a2 a3 a4 a5 a6 a7)]) ;2
  ;; should be 2⁸= 256 steps
  (by-destruct a1)
  (by-destruct a2)
  (by-destruct a3)
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a3)
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a2)
  (by-destruct a3)
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a3)
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a4)
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a5)
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a6)
  (by-destruct a7)
  by-assumption
  by-assumption
  (by-destruct a7)
  by-assumption
  by-assumption)

(check-type beq-string-refl : (∀ [s : String] (== true (string-equal? s s))))

(define (total-map [A : Type]) (-> String A))
(define (t-empty_ [A : Type] [v : A]) (λ [s : String] v))

(define-implicit t-empty = t-empty_ 1)

(define (t-update_ [A : Type] [m : (total-map A)] [x : String] [v : A])
  (λ [y : String] (if (string-equal? x y) v (m y))))

(define-implicit t-update = t-update_ 1)

(define example-map
  (t-update (t-update (t-empty false) "foo" true) "bar" true))

(check-type example-map : (total-map Bool))
(check-type (example-map "foo") : Bool -> true)
(check-type (example-map "bar") : Bool -> true)
(check-type (example-map "bad") : Bool -> false)

(define-syntax (t-updates stx)
  (syntax-parse stx
    [(_ m (~datum &)) #'m]
    [(_ m (~datum &) a (~datum -->) x) #'(t-update m a x)]
    [(_ m (~datum &) a (~datum -->) x (~datum :) . rst)
     #'(t-updates (t-update m a x) & . rst)]))

(define example-map2
  (t-updates (t-empty false) & "foo" --> true : "bar" --> true))

(define-theorem update-example1
  (== (example-map2 "baz") false)
  reflexivity)
(define-theorem update-example2
  (== (example-map2 "foo") true)
  reflexivity)
(define-theorem update-example3
  (== (example-map2 "quux") false)
  reflexivity)
(define-theorem update-example4
  (== (example-map2 "bar") true)
  reflexivity)

(define-theorem t-apply-empty
  (∀ [A : Type] [x : String] [v : A]
     (== ((t-empty v) x) v))
  by-intros
  reflexivity)

(define-theorem t-update-eq
  (∀ [A : Type] [m : (total-map A)] [x : String] [v : A]
     (== ((t-update m x v) x) v))
  by-intros
  (by-rewriteL beq-string-refl)
  reflexivity)

(check-type t-update-eq
  : (∀ [A : Type] [m : (total-map A)] [x : String] [v : A]
     (== ((t-update m x v) x) v)))
