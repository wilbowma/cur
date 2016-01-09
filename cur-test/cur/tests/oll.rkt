#lang cur

;; NB TODO: raco test reports incorrect number of total tests due to
;; beign-for-syntax; but all failing tests correctly raise errors

(require
 rackunit
 cur/stdlib/sugar
 cur/oll)

(begin-for-syntax
  (require rackunit)
  (define (check-id-equal? v1 v2)
    (check-equal?
     (syntax->datum v1)
     (syntax->datum v2)))
  (define (check-id-match? v1 v2)
    (check-regexp-match
     v1
     (symbol->string (syntax->datum v2))))
  (check-id-match?
   #px"term\\d+"
   (fresh-name #'term))
  (check-id-equal?
   #'stlc-lambda
   (new-name #'stlc #'lambda))
  (check-id-match?
   #px"stlc-term\\d+"
   (new-name #'stlc (fresh-name #'term))))

(begin-for-syntax
  (check-equal?
   (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
           (format "\\mbox{\\textit{term}} & e & \\bnfdef & (e1 e2) \\bnfalt (lambda (x) e)\\\\~n"))
   (output-latex-bnf #'(x)
                     #'((term (e) ::= (e1 e2) (lambda (x) e)))))
  (check-equal?
   (format "$$\\begin{array}{lrrl}~n~a~n\\end{array}$$"
           (format "\\mbox{\\textit{type}} & A,B,C & \\bnfdef & unit \\bnfalt (* A B) \\bnfalt (+ A C)\\\\~n"))
   (output-latex-bnf #'(x)
                     #'((type (A B C) ::= unit (* A B) (+ A C))))))

(check-equal?
 (var-equal? (avar z) (avar z))
 true)
(check-equal?
 (var-equal? (avar z) (avar (s z)))
 false)

(begin-for-syntax
  (check-equal?
   (parameterize ([coq-defns ""]) (output-coq #'(data nat : Type (z : nat))) (coq-defns))
   (format "Inductive nat : Type :=~n| z : nat.~n"))
  (check-regexp-match
   "(forall .+ : Type, Type)"
   (output-coq #'(-> Type Type)))
  (let ([t (parameterize ([coq-defns ""])
             (output-coq #'(define-relation (meow gamma term type)
                             [(g : gamma) (e : term) (t : type)
                              --------------- T-Bla
                              (meow g e t)]))
             (coq-defns))])
    (check-regexp-match
     "Inductive meow : \\(forall .+ : gamma, \\(forall .+ : term, \\(forall .+ : type, Type\\)\\)\\) :="
     (first (string-split t "\n")))
    (check-regexp-match
     "\\| T-Bla : \\(forall g : gamma, \\(forall e : term, \\(forall t : type, \\(\\(\\(meow g\\) e\\) t\\)\\)\\)\\)\\."
     (second (string-split t "\n"))))
  (let ([t (output-coq #'(elim nat Type (lambda (x : nat) nat) z
                               (lambda* (x : nat) (ih-x : nat) ih-x)
                               e))])
    (check-regexp-match
     "\\(\\(\\(\\(nat_rect \\(fun x : nat => nat\\)\\) z\\) \\(fun x : nat => \\(fun ih_x : nat => ih_x\\)\\)\\) e\\)"
     t))
  (check-regexp-match
   "Definition thm_plus_commutes := \\(forall n : nat, \\(forall m : nat, \\(\\(\\(== nat\\) \\(\\(plus n\\) m\\)\\) \\(\\(plus m\\) n\\)\\)\\)\\).\n"
   (parameterize ([coq-defns ""])
     (output-coq #'(define thm:plus-commutes (forall* (n : nat) (m : nat)
                                                      (== nat (plus n m) (plus m n)))))
     (coq-defns)))
  (check-regexp-match
   "Function add1 \\(n : nat\\)  := \\(s n\\).\n"
   (parameterize ([coq-defns ""])
     (output-coq #'(define (add1 (n : nat)) (s n)))
     (coq-defns))))
