#lang cur
(require
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/maybe
 cur/stdlib/list
 rackunit/turnstile)

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
(check-type (list-ref Bool z (nil Bool))
            : (Maybe Bool)
            -> (none Bool))
(check-type (list-ref Bool (s z) (nil Bool))
            : (Maybe Bool)
            -> (none Bool))
(check-type (list-ref Bool (s (s z)) (nil Bool))
            : (Maybe Bool)
            -> (none Bool))
(check-type (list-ref Bool z (cons Bool true (nil Bool)))
            : (Maybe Bool)
            -> (some Bool true))
(check-type (list-ref Bool z (cons Bool false (cons Bool true (nil Bool))))
            : (Maybe Bool)
            -> (some Bool false))
(check-type (list-ref Bool (s z) (cons Bool false (cons Bool true (nil Bool))))
            : (Maybe Bool)
            -> (some Bool true))
(check-type (list-ref Bool (s (s z)) (cons Bool false (cons Bool true (nil Bool))))
            : (Maybe Bool)
            -> (none Bool))

;; list-ref: non-full applications
(check-type list-ref : (Π [A : Type] (-> Nat (List A) (Maybe A))))
(check-type (list-ref Bool) : (-> Nat (List Bool) (Maybe Bool)))
(check-type (list-ref Nat) : (-> Nat (List Nat) (Maybe Nat)))
(check-type (list-ref (List Nat)) : (-> Nat (List (List Nat)) (Maybe (List Nat))))
(check-type (list-ref Bool z) : (-> (List Bool) (Maybe Bool)))
(typecheck-fail (list-ref Bool z (nil Nat))
                #:with-msg "expected \\(List Bool\\), given \\(List Nat\\)")

(check-type ((list-ref Bool z) (nil Bool)) : (Maybe Bool) -> (none Bool))

(check-type (length Nat (nil Nat)) : Nat -> 0)
(check-type (length Bool (nil Bool)) : Nat -> 0)
(typecheck-fail (length Bool (nil Nat))
                #:with-msg "expected \\(List Bool\\), given \\(List Nat\\)")

(check-type (length Nat (cons Nat z (nil Nat))) : Nat -> 1)

(check-type
 (list-append Nat (nil Nat) (nil Nat))
 : (List Nat)
 -> (nil Nat))

(check-type
 (list-append Nat (cons Nat z (nil Nat)) (nil Nat))
 : (List Nat)
 -> (cons Nat z (nil Nat)))

(check-type
 (list-append Nat (cons Nat (s z) (nil Nat)) (cons Nat z (nil Nat)))
 : (List Nat)
 -> (cons Nat z (cons Nat (s z) (nil Nat))))

(check-type
 (length Nat (list-append Nat (cons Nat z (nil Nat)) (cons Nat (s z) (nil Nat))))
 : Nat
 -> 2)

;; list-append: non-full applications
;; - slightly differs from list-ref bc post-non-matching arg uses tyvar (ie, ls2)
(check-type (list-append Nat) : (-> (List Nat) (List Nat) (List Nat)))
(check-type ((list-append Nat) (nil Nat)) : (-> (List Nat) (List Nat)))
(check-type (((list-append Nat) (nil Nat)) (nil Nat)) : (List Nat) -> (nil Nat))
(typecheck-fail (((list-append Nat) (nil Nat)) (nil Bool))
                  #:with-msg "expected \\(List Nat\\), given \\(List Bool\\)")

;; non-full app, with non-nil args: exercises the 2nd match clause
(check-type (cons Nat 1 (nil Nat)) : (List Nat))
(check-type ((list-append Nat) (cons Nat 1 (nil Nat))) : (-> (List Nat) (List Nat)))
