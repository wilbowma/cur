#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label (only-meta-in 0 cur/stdlib/typeclass))
  (for-label (only-meta-in 0 cur/stdlib/nat))
  (for-label (only-meta-in 0 cur/stdlib/bool))
  (for-label (except-in cur/stdlib/sugar :))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/typeclass cur/stdlib/bool cur/stdlib/nat cur/stdlib/sugar)"))

@title{Typeclass}
@defmodule[cur/stdlib/typeclass]
This library defines some macros that provide ad-hoc polymorphism
similar to typeclasses, although lacking some of the crucial features
of typeclasses such as typeclass constraints. These typeclasses are
added entirely through meta-programming.

@defform[(typeclass (class (param : Type)) (name : t) ...)]{
Declares a new typeclass named @racket[class], whose parameter
@racket[param] has type @racket[Type]. Implementations of this
typeclass must define of the methods @racket[name ...] whose types
are @racket[t ...].

@examples[#:eval curnel-eval
          (typeclass (Eqv (A : Type))
          (equal? : (-> (a : A) (b : A) Bool)))]
}

@defform[(impl (class param) defs ...)]{
Provides an implementation of the typeclass @racket[class] for the
type @racket[param]. The defintions @racket[defs ...] are Cur
definitions for each of the methods of the typeclass.

@examples[#:eval curnel-eval
          (impl (Eqv Bool)
            (define (equal? (a : Bool) (b : Bool))
              (if a
                  (if b true false)
                  (if b false true))))
          (impl (Eqv Nat)
            (define equal? nat-equal?))
          (equal? true true)
          (equal? z z)]
}
