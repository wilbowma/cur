#lang cur

;; NB TODO: raco test reports incorrect number of total tests due to
;; beign-for-syntax; but all failing tests correctly raise errors

(require
 rackunit
 cur/stdlib/sugar
 cur/stdlib/nat
 cur/stdlib/bool
 cur/stdlib/prop
 cur/olly)

(begin-for-syntax
  (require rackunit))

;; Can't test this way anymore.
#;(begin-for-syntax
  (check-equal?
   (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
           (format "\\mbox{\\textit{term}} & e & \\bnfdef & (e1 e2) \\bnfalt (lambda (x) e)\\\\~n"))
   (typeset-bnf #'((term (e) ::= (e1 e2) (lambda (x) e)))))
  (check-equal?
   (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
           (format "\\mbox{\\textit{type}} & A,B,C & \\bnfdef & unit \\bnfalt (* A B) \\bnfalt (+ A C)\\\\~n"))
   (typeset-bnf #'((type (A B C) ::= unit (* A B) (+ A C))))))

(begin-for-syntax
  (check-equal?
   (format "Inductive nat : Type :=~n| z : nat.~n")
   (cur->coq #'(data nat : Type (z : nat))))
  (check-regexp-match
   "(forall .+ : Type, Type)"
   (cur->coq #'(-> Type Type)))
  (let ([t (cur->coq
            #'(define-relation (meow Nat Bool Type)
                [(g : Nat) (e : Bool) (t : Type)
                 --------------- T-Bla
                 (meow g e t)]))])
    (check-regexp-match
     "Inductive meow : \\(forall .+ : Nat, \\(forall .+ : Bool, \\(forall .+ : Type, Type\\)\\)\\) :="
     (first (string-split t "\n")))
    (check-regexp-match
     "\\| T_Bla : \\(forall g : Nat, \\(forall e : Bool, \\(forall t : Type, \\(\\(\\(meow g\\) e\\) t\\)\\)\\)\\)\\."
     (second (string-split t "\n"))))
  (let ([t (cur->coq
            #'(elim Nat (lambda (x : Nat) Nat)
                    ()
                    (z (lambda (x : Nat) (ih-x : Nat) ih-x))
                    e))])
    (check-regexp-match
     "Eval compute in \\(Nat_rect \\(fun x : Nat => Nat\\) z \\(fun x : Nat => \\(fun ih_x : Nat => ih_x\\)\\) e\\)."
     t))
  (check-regexp-match
   "Definition thm_plus_commutes := \\(forall n : Nat, \\(forall m : Nat, \\(\\(\\(== Nat\\) \\(\\(plus n\\) m\\)\\) \\(\\(plus m\\) n\\)\\)\\)\\).\n"
   (cur->coq
    #'(define thm:plus-commutes (forall (n : Nat) (m : Nat)
                                        (== Nat (plus n m) (plus m n))))))
  (check-regexp-match
   "Function add1 \\(n : Nat\\)  := \\(s n\\).\n"
   (cur->coq #'(define (add1 (n : Nat)) (s n)))))
