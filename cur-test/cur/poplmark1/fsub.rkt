#lang cur

;; Challenge 1A: Transitivity of Subtyping in System F with Subtyping (F_sub)

;; First, the syntax

#|
Below is the code I would like to write.

  (define-data/bnf F-Type (T) ::= α | Top | (T -> T) | (∀ α <: T. T))
  (define-data/bnf F-Env (Γ) ::= ∅ | (Γ, α <: T))

But, this has two problems:
- [ ] Binding; how does it know that ∀ binds?
- [ ] Parsing; how do the user get to write this code instead of manually
      writing the inductive constructors.
- [ ] Pretty-printing; error messages will almost certainly show inductive
      definitions instead of this pretty notation.

So, perhaps for binding:

  (define-data/bnf F-Type (T) ::= α #:name | Top | (T -> T) | (∀ α #:bind-name <: T . T #:refers-to (α)))
  (define-data/bnf F-Env  (Γ) ::= ∅ | (Γ, α #:bind-name <: T #:refers-to Γ) #:exports (Γ α))

Annotations to what subterms reference bound names (#:refers-to, #:name), and
for "exporting" names into recursive structures (#:exports).
Loosely based on Redex's binding magic.

For parsing:

(define-data/bnf F-Type (T) ::= α #:name | Top | (T -> T) | (∀ α #:bind-name <: T . T #:refers-to (α))
  ;; Parser should take a syntax object, representing on of the productions of
  ;; the BNF, and a list of constructors (ctors) which contain the underlying
  ;; representation of constructors for each of the productions.
  ;; The parser must return a fully parsed syntax object, i.e., a syntax object
  ;; with one of the constructors applied to Cur terms.

  ;; In many cases, like this, the parser should be easy to infer.
  #:parser (lambda (stx ctors)
             (let loop ([stx stx])
               (syntax-parse stx
                 #:literals (Top -> <: ∀)
                 ;; Names are held abstract; you must match on them with the
                 ;; syntax-pattern ~name, and the constructor for bound names takes
                 ;; the name as an argument
                 [(~name x)
                  (quasisyntax/loc stx
                    (#,(first ctors) x))]
                 [Top
                  (quasisyntax/loc stx
                    #,(second ctors))]
                 [(T1 -> T2)
                  (quasisyntax/loc stx
                    (#,(third ctors)
                     #,(loop #'T1)
                     #,(loop #'T2)))]
                 [(∀ (~name x) <: T1 . T2)
                  (quasisyntax/loc stx
                    (#,fourth ctors
                     #,(loop #'T1)
                     #,(bind #'x (loop #'T2))))]))))

Use:
(bnf T α) -> binding error
(bnf T (∀ α <: Top . (α -> α))) -> okay

(bnf T (∀ α <: Top . ,((lambda (x : Unit) (bnf T α) unit)))) -> okay

Probably want a parameter for which grammar is currently being parsed, or some
way of detecting which grammar.

For pretty printing:

Need to be enable to attach a pretty printing routine to constructors, for
example, via a syntax property.
The bnf grammar would generate such a routine automatically, or optionally,
allow the user to provide one, like the parser.
The hard part is how to print binding structure.
Need to reify the representation of names into named identifiers for printing.
|#
