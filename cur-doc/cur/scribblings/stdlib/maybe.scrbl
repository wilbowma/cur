#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label (only-meta-in 0 cur/stdlib/maybe))
  (for-label (only-meta-in 0 cur/stdlib/bool))
  (for-label (except-in cur/stdlib/sugar :))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/bool cur/stdlib/maybe cur/stdlib/sugar)"))

@title{Maybe}
@defmodule[cur/stdlib/maybe]
This library defines the datatype @racket[Maybe] and several forms for using them.

@; TODO: Define a @defdata macro for Cur
@deftogether[(@defthing[#:kind "1 parameter type" Maybe (-> (A : Type) Type)]
              @defthing[#:kind "constructor" none (-> (A : Type) (Maybe A))]
              @defthing[#:kind "constructor" some (-> (A : Type) (a : A) (Maybe A))])]{
The maybe datatype.
}

@defform[(some/i a)]{
A syntactic form for @racket[some] that attempts to infer the type of the expression @racket[a] to reduce annotation burden.

@examples[#:eval curnel-eval
          (some Bool true)
          (some/i true)]
}
