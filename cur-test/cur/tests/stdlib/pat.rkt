#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/equality
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 rackunit/turnstile+)

;; tests for pattern matching in define/rec/match (from stdlib/sugar)

;; tests for return type mismatch
(typecheck-fail/toplvl
 (define/rec/match sub1-bad1 : Bool -> Nat
   [z => z]
   [(s x) => x])
 #:with-msg "expected pattern for type Bool, given pattern for.*Nat.*z")

(typecheck-fail/toplvl
 (define/rec/match sub1-bad2 : Nat -> Bool
   [z => z]
   [(s x) => x])
 #:with-msg "expected Bool, given Nat.*expression: z")

;; tests for failed termination check

(typecheck-fail/toplvl
 (define/rec/match bad-plus : Nat [n : Nat] -> Nat
   [z => n]
   [(s x) => (bad-plus (s x) n)])
 #:with-msg "type mismatch.*s x")

(typecheck-fail/toplvl
 (define/rec/match bad-minus : Nat Nat -> Nat
   [z _ => z]
   [(s n-1) z => (s n-1)]
   [(s n-1) (s m-1) => (bad-minus n-1 (s m-1))])
 #:with-msg "type mismatch.*s m-1")

; more examples, courtesy of issue #93
(typecheck-fail/toplvl
  (define/rec/match bang! : Nat -> (== 0 1)
    [n => (bang! n)])
 #:with-msg "type mismatch.*n")

(typecheck-fail/toplvl
  (define/rec/match bang!1 : [n : Nat] -> (== 0 1)
    [=> (bang!1 n)])
 #:with-msg "type mismatch.*n")

(typecheck-fail/toplvl
  (define/rec/match bang!2 : -> (== 0 1)
    [=> (bang!2)])
 #:with-msg "must have at least one argument for pattern matching")

(typecheck-fail/toplvl
(define/rec/match bad-rec-pat? : Nat -> Bool
  [z => true]
  [(s z) => false]
  [(s (s x)) => (bad-rec-pat? (s x))])
 #:with-msg "type mismatch.*s x")

(define/rec/match multi-pat : Nat Nat Nat -> Nat
  [_ _ z => 0]
  [n m (s l-1) => (multi-pat n m l-1)])

;; from Gimenez 1995
;; example that is easy for pattern match, hard with Nat elim
(define/rec/match even? : Nat -> Bool
  [z => true]
  [(s z) => false]
  [(s (s x)) => (even? x)])

(check-type even? : (-> Nat Bool))
(check-type (even? 0) : Bool -> true)
(check-type (even? 1) : Bool -> false)
(check-type (even? 2) : Bool -> true)
(check-type (even? 3) : Bool -> false)
(check-type (even? 4) : Bool -> true)
(check-type (even? 5) : Bool -> false)

(define-datatype V : Type
  [cnsv : (-> (Π [A : Type] (-> A A)) V)])

(typecheck-fail/toplvl
 (define/rec/match f : V -> False
   [(cnsv h) => (f (h V (cnsv h)))])
 #:with-msg "type mismatch.*h V")
