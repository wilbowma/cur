#lang scribble/manual

@(require
  "../defs.rkt"
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/bool cur/stdlib/nat cur/stdlib/sugar cur/stdlib/list)"))

@title{List}
@defmodule[cur/stdlib/list]
This library defines the datatype @racket[List] and several functions on them.

@deftogether[(@defthing[List (-> Type Type)]
              @defthing[nil (forall (A : Type) (List A))]
	      @defthing[cons (forall (A : Type) (a : A) (-> (List A) (List A)))])]{
The polymorphic list datatype.
}

@defproc[(list-ref [A Type] [ls (List A)] [n Nat]) (Maybe A)]{
Returns the @racket[n]th element of @racket[ls] in the @racket[Maybe] monad.
}
