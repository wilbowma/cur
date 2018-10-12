#lang cur
(require
 turnstile/rackunit-typechecking
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/maybe
 cur/stdlib/list)

(check-type (nil Nat) : (List Nat) -> (nil Nat))
(check-not-type (nil Nat) : (List Bool))

(check-type (cons Bool true (nil Bool)) : (List Bool))

(check-type (build-list Nat) : (List Nat) -> (nil Nat))
(check-type (build-list Nat z) : (List Nat) -> (cons Nat z (nil Nat)))
(check-type (build-list Nat z z) : (List Nat) -> (cons Nat z (cons Nat z (nil Nat))))

(check-type
 (lambda (A : Type) (a : A)
         (ih-a : (-> Nat (Maybe A)))
         (n : Nat)
         (match n #:return (Maybe A)
           [z (some A a)]
           [(s (n-1 : Nat))
            (ih-a n-1)]))
 : (Π (A : Type) (a : A) (ih-a : (-> Nat (Maybe A)))
      (n : Nat)
      (Maybe A)))
(check-type
 (lambda (A : Type) (n : Nat) (none A))
 : (Π (A : Type) (-> Nat (Maybe A))))
(check-type
 (elim-List (nil Bool)
            (lambda (ls : (List Bool)) Nat)
            z
            (lambda (a : Bool) (ls : (List Bool)) (ih : Nat)
                    z))
 : Nat)

;; list-ref
(check-type (list-ref Bool (nil Bool) z)
            : (Maybe Bool)
            -> (none Bool))
(check-type (list-ref Bool (nil Bool) (s z))
            : (Maybe Bool)
            -> (none Bool))
(check-type (list-ref Bool (nil Bool) (s (s z)))
            : (Maybe Bool)
            -> (none Bool))
(check-type (list-ref Bool (cons Bool true (nil Bool)) z)
            : (Maybe Bool)
            -> (some Bool true))
(check-type (list-ref Bool (cons Bool false (cons Bool true (nil Bool))) z)
            : (Maybe Bool)
            -> (some Bool false))
(check-type (list-ref Bool (cons Bool false (cons Bool true (nil Bool))) (s z))
            : (Maybe Bool)
            -> (some Bool true))
(check-type (list-ref Bool (cons Bool false (cons Bool true (nil Bool))) (s (s z)))
            : (Maybe Bool)
            -> (none Bool))

;; list-ref: non-full applications
(check-type list-ref : (Π [A : Type] (-> (List A) Nat (Maybe A))))
(check-type (list-ref Bool) : (-> (List Bool) Nat (Maybe Bool)))
(check-type (list-ref Nat) : (-> (List Nat) Nat (Maybe Nat)))
(check-type (list-ref (List Nat)) : (-> (List (List Nat)) Nat (Maybe (List Nat))))
(check-type (list-ref Bool (nil Bool)) : (-> Nat (Maybe Bool)))
;; TODO: fix this err msg
(typecheck-fail (list-ref Bool (nil Nat))
;                #:with-msg "expected (List Bool), given (List Nat)")
                #:with-msg "expected \\(List A\\), given \\(List A\\)")
(check-type ((list-ref Bool (nil Bool)) z) : (Maybe Bool) -> (none Bool))

(check-type (length Nat (nil Nat)) : Nat -> 0)
(check-type (length Bool (nil Bool)) : Nat -> 0)
;; TODO: fix this err msg
(typecheck-fail (length Bool (nil Nat))
;                #:with-msg "expected (List Bool), given (List Nat)")
                #:with-msg "expected \\(List A\\), given \\(List A\\)")
(check-type (length Nat (cons Nat z (nil Nat))) : Nat -> 1)

(check-type
 (list-append Nat (nil Nat) (nil Nat))
 : (List Nat)
 -> (nil Nat))

(check-type
 (list-append Nat (nil Nat) (cons Nat z (nil Nat)))
 : (List Nat)
 -> (cons Nat z (nil Nat)))

(check-type
 (list-append Nat (cons Nat z (nil Nat)) (cons Nat (s z) (nil Nat)))
 : (List Nat)
 -> (cons Nat z (cons Nat (s z) (nil Nat))))

(check-type
 (length Nat (list-append Nat (cons Nat z (nil Nat)) (cons Nat (s z) (nil Nat))))
 : Nat
 -> 2)
