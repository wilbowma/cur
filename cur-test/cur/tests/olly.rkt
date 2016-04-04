#lang cur

;; NB TODO: raco test reports incorrect number of total tests due to
;; beign-for-syntax; but all failing tests correctly raise errors

(require
 rackunit
 cur/stdlib/sugar
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
            #'(define-relation (meow gamma term type)
                [(g : gamma) (e : term) (t : type)
                 --------------- T-Bla
                 (meow g e t)]))])
    (check-regexp-match
     "Inductive meow : \\(forall .+ : gamma, \\(forall .+ : term, \\(forall .+ : type, Type\\)\\)\\) :="
     (first (string-split t "\n")))
    (check-regexp-match
     "\\| T_Bla : \\(forall g : gamma, \\(forall e : term, \\(forall t : type, \\(\\(\\(meow g\\) e\\) t\\)\\)\\)\\)\\."
     (second (string-split t "\n"))))
  (let ([t (cur->coq
            #'(elim nat (lambda (x : nat) nat)
                    ()
                    (z (lambda (x : nat) (ih-x : nat) ih-x))
                    e))])
    (check-regexp-match
     "\\(nat_rect \\(fun x : nat => nat\\) z \\(fun x : nat => \\(fun ih_x : nat => ih_x\\)\\) e\\)"
     t))
  (check-regexp-match
   "Definition thm_plus_commutes := \\(forall n : nat, \\(forall m : nat, \\(\\(\\(== nat\\) \\(\\(plus n\\) m\\)\\) \\(\\(plus m\\) n\\)\\)\\)\\).\n"
   (cur->coq
    #'(define thm:plus-commutes (forall (n : nat) (m : nat)
                                        (== nat (plus n m) (plus m n))))))
  (check-regexp-match
   "Function add1 \\(n : nat\\)  := \\(s n\\).\n"
   (cur->coq #'(define (add1 (n : nat)) (s n)))))
