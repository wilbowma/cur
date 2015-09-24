#lang scribble/manual

@(require "../defs.rkt")

@;(TODO Move this to defs.rkt)
@(require racket/sandbox scribble/eval)
@(define curnel-eval
   (parameterize ([sandbox-output 'string]
                  [sandbox-error-output 'string]
                  [sandbox-eval-limits #f]
                  [sandbox-memory-limit #f])
     (make-module-evaluator "#lang cur (require cur/stdlib/bool) (require cur/stdlib/sugar)")))


@title{Sugar}
The @tech{curnel forms} are sort of terrible for actually writing code. Functions and applications are
limited to single artity. Functions type must be specified using the dependent @racket[forall], even
when the dependency is not used. Inductive elimination can only be done via the primitive eliminator
and not via pattern matching. However, with the full force of Racket's syntactic extension system, we
can define not only simply notation, but redefine what application means, or define a pattern matcher
that expands into the eliminator.

@defmodule[cur/stdlib/sugar]
This library defines various syntactic extensions making Cur easier to write than writing raw TT.

@defform[(-> t1 t2)]{
A non-dependent function type Equivalent to @racket[(forall (_ : t1) t2)], where @racket[_] indicates an variable that is not used.

@examples[#:eval curnel-eval
          (data And : (-> Type (-> Type Type))
            (conj : (forall (A : Type) (forall (B : Type) (-> A (-> B ((And A) B)))))))
          ((((conj Bool) Bool) true) false)]
}

@defform[(->* t ...)]{
A non-dependent multi-arity function type that supports automatic currying.

@examples[#:eval curnel-eval
          (data And : (->* Type Type Type)
            (conj : (forall (A : Type) (forall (B : Type) (->* A B ((And A) B))))))
          ((((conj Bool) Bool) true) false)]
}


@defform[(forall* (a : t) ... type)]{
A multi-arity function type that supports automatic currying.

@examples[#:eval curnel-eval
          (data And : (->* Type Type Type)
            (conj : (forall* (A : Type) (B : Type)
                      (->* A B ((And A) B)))))
          ((((conj Bool) Bool) true) false)]

}

@defform[(lambda* (a : t) ... body)]{
Defines a multi-arity procedure that supports automatic currying.

@examples[#:eval curnel-eval
          ((lambda (x : Bool) (lambda (y : Bool) y)) true)
          ((lambda* (x : Bool) (y : Bool) y) true)
          ]
}

@defform[(#%app f a ...)]{
Defines multi-arity procedure application via automatic currying.

@examples[#:eval curnel-eval
          (data And : (->* Type Type Type)
            (conj : (forall* (A : Type) (B : Type)
                      (->* A B ((And A) B)))))
          (conj Bool Bool true false)]
}

@defform*[((define name body)
           (define (name (x : t) ...) body))]{
Like the @racket[define] provided by @racketmodname[cur/curnel/redex-lang], but supports
defining curried functions via @racket[lambda*].
}

@defform*[((define-type name type)
           (define-type (name (a : t) ...) body))]{
Like @racket[define], but uses @racket[forall*] instead of @racket[lambda*].
}

@defform[(case* e [pattern maybe-IH body] ...)
         #:grammar
         [(pattern
            constructor
            (code:line)
            (code:line (constructor (x : t) ...)))
          (maybe-IH
            (code:line)
            (code:line IH: ((x : t) ...)))]]{
A pattern-matcher-like syntax for inductive elimination. Actually does not do pattern matching and
relies on the constructors patterns being specified in the same order as when the inductive type was
defined.

@examples[#:eval curnel-eval
          (require cur/stdlib/nat)
          (case z
            [z true]
            [(s (n : Nat))
             IH: ((_ : Bool))
             false])]
}
