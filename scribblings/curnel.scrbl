#lang scribble/manual

@(require
  "defs.rkt"
  scribble/eval)

@title{Curnel Forms}
@deftech{Curnel forms} are the core forms provided @racketmodname[cur].
These forms come directly from the trusted core and are all that remain after macro expansion.
@todo{Link to guide regarding macro expansion}
The core of @racketmodname[cur] is essentially TT with an impredicative universe @racket[(Type 0)].
For a very understandable in-depth look at TT, see chapter 2 of
@hyperlink["https://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf"
           "Practical Implementation of a Dependently Typed Functional Programming Language"], by
Edwin C. Brady.

@(define curnel-eval (curnel-sandbox ""))

@defform*[((Type n)
	   Type)]{
Define the universe of types at level @racket[n], where @racket[n] is any natural number.
@racket[Type] is a synonym for @racket[(Type 0)]. Cur is impredicative
in @racket[(Type 0)], although this is likely to change to a more
restricted impredicative universe.

@examples[#:eval curnel-eval
          (Type 0)]

@examples[#:eval curnel-eval
          (Type 1)]

@examples[#:eval curnel-eval
          Type]
}

@defform*[((lambda (id : type-expr) body-expr)
           (λ (id : type-expr) body-expr))]{
Produces a single arity procedure, binding the identifier @racket[id] of type @racket[type-expr] in @racket[body-expr] and in the type of
@racket[body-expr].
Both @racket[type-expr] and @racket[body-expr] can contain non-curnel forms, such as macros.

Currently, Cur will return the underlying representation of a procedure when a @racket[lambda] is
evaluated at the top-level. Do not rely on this representation.

@examples[#:eval curnel-eval
          (lambda (x : Type) x)]

@examples[#:eval curnel-eval
          (λ (x : Type) (lambda (y : x) y))]


@defform[(#%app procedure argument)]{
Applies the single arity @racket[procedure] to @racket[argument].
}

@examples[#:eval curnel-eval
          ((lambda (x : (Type 1)) x) Type)]

@examples[#:eval curnel-eval
          (#%app (lambda (x : (Type 1)) x) Type)]
}

@defform*[((forall (id : type-expr) body-expr)
           (∀ (id : type-expr) body-expr))]{
Produces a dependent function type, binding the identifier @racket[id] of type @racket[type-expr] in @racket[body-expr].


@examples[#:eval curnel-eval
          (forall (x : Type) Type)]

@examples[#:eval curnel-eval
          (lambda (x : (forall (x : (Type 1)) Type))
            (x Type))]
}

@defform[(data id : type-expr (id* : type-expr*) ...)]{
Defines an inductive datatype named @racket[id] of type @racket[type-expr], with constructors
@racket[id*] each with the corresponding type @racket[type-expr*].
Currently, Cur does not attempt to ensure the well-foundedness of the inductive definition.
For instance, Cur does not currently perform strict positivity checking.

@examples[#:eval curnel-eval
          (data Bool : Type
                (true : Bool)
                (false : Bool))
          ((lambda (x : Bool) x) true)
          (data False : Type)
          (data And : (forall (A : Type) (forall (B : Type) Type))
            (conj : (forall (A : Type) (forall (B : Type) (forall (a : A) (forall (b : B) ((And A) B)))))))
          ((((conj Bool) Bool) true) false)]
}

@defform[(elim type motive-universe)]{
Returns the inductive eliminator for @racket[type] where the @racket[motive-universe] is the universe
of the motive.
The eliminator expects the next argument to be the motive, the next @racket[N] arguments to be the methods for
each of the @racket[N] constructors of the inductive type @racket[type], the next @racket[P] arguments
to be the parameters @racket[p_0 ... p_P] of the inductive @racket[type], and the final argument to be the term to
eliminate of type @racket[(type p_0 ... p_P)].

The following example runs @racket[(sub1 (s z))].

@examples[#:eval curnel-eval
          (data Nat : Type
            (z : Nat)
            (s : (forall (n : Nat) Nat)))
          (((((elim Nat Type)
              (lambda (x : Nat) Nat))
             z)
            (lambda (n : Nat) (lambda (IH : Nat) n)))
           (s z))]
}

@defform[(define id expr)]{
Binds @racket[id] to the result of @racket[expr].

@examples[#:eval curnel-eval
          (data Nat : Type
            (z : Nat)
            (s : (forall (n : Nat) Nat)))
          (define sub1 (lambda (n : Nat)
                         (((((elim Nat Type) (lambda (x : Nat) Nat))
                           z)
                          (lambda (n : Nat) (lambda (IH : Nat) n))) n)))
          (sub1 (s (s z)))
          (sub1 (s z))
          (sub1 z)]
}
@todo{Document @racket[require] and @racket[provide]}
