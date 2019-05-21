#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/sized
 cur/stdlib/bool
 cur/stdlib/prop
 cur/stdlib/list
 rackunit/turnstile)

;; tests for pattern matching in define/rec/match (from stdlib/sugar)

;; tests for return type mismatch
(typecheck-fail/toplvl
 (define/rec/match2 sub1-bad1 : Bool -> Nat
   [z => z]
   [(s x) => x])
 #:with-msg "expected pattern for type Bool, given pattern for.*Nat.*z")

(typecheck-fail/toplvl
 (define/rec/match2 sub1-bad2 : Nat -> Bool
   [z => z]
   [(s x) => x])
 #:with-msg "expected Bool, given Nat.*expression: z")

;; tests for failed termination check

(typecheck-fail/toplvl
 (define/rec/match2 bad-plus : Nat [n : Nat] -> Nat
   [z => n]
   [(s x) => (bad-plus (s x) n)])
 #:with-msg "type mismatch.*s x")

;; sized datatype wrapper ----------------------------------------

;; sz \in Size = id | (< sz) | #f, where #f = inf size
;; 
;; subtyping rel:
;; i <: i
;; (< i) <: i
;; (< i) <: i
;; _ <: #f
;; (< (< i)) <: (< i) etc

;; sized nat

(define-sized-datatype Nat) ; constructor generates fresh size if args are unsized

(require "rackunit-size.rkt")
(define ze1 (z/sz))
(define ze2 (z/sz))
;; (print-sz ze1)
;; (print-sz ze2)
(check-noninf-sz ze1)
(check-noninf-sz ze2)
(check-noninf-sz (s/sz ze1))

;; from Gimenez 1995
;; example that is easy for pattern match, hard with Nat elim
(define/rec/match2 even? : Nat -> Bool
  [z/sz => true]
  [(s/sz z) => false]
  [(s/sz (s/sz x)) => (even? x)])

(check-type even? : (-> Nat Bool))
(check-type (even? 0) : Bool -> true)
(check-type (even? 1) : Bool -> false)
(check-type (even? 2) : Bool -> true)
(check-type (even? 3) : Bool -> false)
(check-type (even? 4) : Bool -> true)
(check-type (even? 5) : Bool -> false)

(define-datatype V : Type
  [cnsv : (-> (Π [A : Type] (-> A A)) V)])

(define-sized-datatype V)

(typecheck-fail/toplvl
 (define/rec/match2 f : V -> False
   [(cnsv/sz h) => (f (h V (cnsv h)))])
 #:with-msg "type mismatch.*h V")

;; examples from Abel 2010

;; tests defining size-preserving fn
(define/rec/match2 pred/sz : [n : Nat #:size i] -> Nat #:size i
  [z/sz => n]
  [(s/sz x) => x])

(typecheck-fail/toplvl
 (define/rec/match2 pred/sz-bad : [n : Nat #:size i] -> Nat #:size i
   [z/sz => z] ; unsized z
   [(s/sz x) => x])
 #:with-msg "expected i, given inf")

(typecheck-fail/toplvl
 (define/rec/match2 pred/sz-bad : [n : Nat #:size i] -> Nat #:size i
   [z/sz => (z/sz)] ; non-matching size
   [(s/sz x) => x])
 #:with-msg "expected i, given")

(define/rec/match2 pred/sz-bad-but-ok : [n : Nat #:size i] -> Nat #:size i
  [z/sz => n]
  [(s/sz x) => n]) ; not correct but size ok

(check-type (pred/sz z) : Nat -> z)
(check-type (pred/sz (s z)) : Nat -> z)
(check-type (pred/sz (s (s z))) : Nat -> (s z))
(check-type (pred/sz (z/sz)) : Nat -> z)
(check-type (pred/sz (s/sz (z/sz))) : Nat -> z)
(check-type (pred/sz (s/sz (s/sz (z/sz)))) : Nat -> (s z))
(check-noninf-sz (pred/sz (z/sz)))
(check-noninf-sz (pred/sz (s/sz (z/sz))))

(define/rec/match2 minus/sz : [n : Nat #:size i] [m : Nat] -> Nat #:size i
  [z/sz _ => n]
  [_ z/sz => n]
  [(s/sz n-1) (s/sz m-1) => (minus/sz n-1 m-1)])

(check-noninf-sz (minus/sz ze1 ze2))

(check-type (minus/sz 4 1) : Nat -> 3)
(check-type (minus/sz 0 0) : Nat -> 0)
(check-type (minus/sz 1 1) : Nat -> 0)
(check-type (minus/sz 1 0) : Nat -> 1)
(check-type (minus/sz 2 0) : Nat -> 2)
(check-type (minus/sz 2 1) : Nat -> 1)
(check-type (minus/sz 3 1) : Nat -> 2)

(typecheck-fail/toplvl
 (define/rec/match2 minus*bad1 : [n : Nat #:size i] [m : Nat] -> Nat #:size i
   [z/sz _ => n]
   [_ z/sz => n]
   [(s/sz n-1) (s/sz m-1) => (minus*bad1 n m-1)]) ; n must be decreasing arg
 #:with-msg "expected \\(\\< i\\), given i")

(define/rec/match2 minus*bad-but-ok1 : [n : Nat #:size i] [m : Nat] -> Nat #:size i
  [z/sz _ => n]
  [_ z/sz => n]
  [(s/sz n-1) (s/sz m-1) => (minus*bad-but-ok1 n-1 m)]) ; m nondecreasing ok

(typecheck-fail/toplvl
 (define/rec/match2 minus*bad3 : [n : Nat #:size i] [m : Nat] -> Nat #:size i
   [z/sz _ => (s n)] ; result not size-preserving
   [_ z/sz => n]
   [(s/sz n-1) (s/sz m-1) => (minus*bad3 n-1 m-1)])
 #:with-msg "expected i, given")

;; TODO: make size types more expressive so example passes?
;; does it work in Agda?
(typecheck-fail/toplvl
 (define/rec/match2 minus*bad2 : [n : Nat #:size i] [m : Nat] -> Nat #:size i
   [z/sz _ => n]
   [_ z/sz => n]
   [(s/sz n-1) (s/sz m-1) => (minus*bad2 (pred/sz (s/sz n-1)) m-1)])
#:with-msg "expected \\(\\< i\\)")


;; this div is semantically wrong;
;; it's purpose is to first that rec case passes (but not size presevation)
(define/rec/match2 div/sz-justrec : [n : Nat #:size i] [m : Nat] -> Nat #:size i
  [z/sz _ => n]
  [(s/sz n-1) _ => (div/sz-justrec (minus/sz n-1 m) m)])

(define/rec/match2 div/sz : [n : Nat #:size i] [m : Nat] -> Nat #:size i
  [z/sz _ => n]
  [(s/sz n-1) _ => (s/sz (div/sz (minus/sz n-1 m) m))])

(check-type (div/sz 0 1) : Nat -> 0)
(check-noninf-sz (div/sz 0 1))
(check-type (div/sz 1 1) : Nat -> 1)
(check-type (div/sz 1 2) : Nat -> 1)
(check-type (div/sz 4 2) : Nat -> 2)
(check-type (div/sz 4 3) : Nat -> 1)

;; list ------------------------------

(define-sized-datatype List)

(define/rec/match2 mapList : [A : Type] [B : Type] [f : (-> A B)] [lst : (List A) #:size i] -> (List B) #:size i
  [_ _ _ (nil/sz _) => (nil/sz #:size i B)]
  [_ _ _ (cons/sz _ a as) => (cons/sz B (f a) (mapList A B f as))])

(define-datatype Rose [A : Type] : Type
  [rose : (-> A (List (Rose A)) (Rose A))])

(define-sized-datatype Rose)

(define nil-rose (nil/sz (Rose Nat)))

(check-noninf-sz nil-rose)
(check-noninf-sz (mapList (Rose Nat) (Rose Nat) (λ [r : (Rose Nat)] r) (nil/sz (Rose Nat))))

(define/rec/match2 mapRose : [A : Type] [B : Type] [f : (-> A B)] [r : (Rose A) #:size i] -> (Rose B) #:size i
  [_ _ _ (rose/sz _ a rs) => (rose/sz B (f a) (mapList (Rose A) (Rose B) (mapRose A B f) rs))])

(check-type
 (mapRose Nat Nat pred/sz (rose/sz Nat 1 (cons (Rose Nat) (rose/sz Nat 2 (nil (Rose Nat)))
                                               (cons (Rose Nat) (rose/sz Nat 3 (nil (Rose Nat)))
                                                     (nil (Rose Nat))))))
 : (Rose Nat)
 -> (rose/sz Nat 0 (cons (Rose Nat) (rose/sz Nat 1 (nil (Rose Nat)))
                         (cons (Rose Nat) (rose/sz Nat 2 (nil (Rose Nat)))
                               (nil (Rose Nat))))))
