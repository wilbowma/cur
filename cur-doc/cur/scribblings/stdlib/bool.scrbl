#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label (only-meta-in 0 cur/stdlib/bool))
  (for-label (only-in (only-meta-in 1 cur/stdlib/bool) bool->meta-bool meta-bool->bool))
  (for-label (only-meta-in 0 cur))
  (for-label (only-in racket/base boolean? displayln))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/bool cur/stdlib/sugar)"))

@title{Bool}
@defmodule[cur/stdlib/bool]
This library defines the datatype @racket[Bool] and several functions and forms for using them.

@; TODO: Define a @defdata macro for Cur
@deftogether[(@defthing[#:kind "0 parameter type" Bool Type]
              @defthing[#:kind "constructor" true Bool]
              @defthing[#:kind "constructor" false Bool])]{
The boolean datatype.
}

@defform[(if test-expr c-expr alt-expr)]{
A syntactic form that expands to the inductive eliminator for @racket[Bool]. This form is currently non-dependent---the branches do not know that @racket[test-expr] is equal to @racket[true] or @racket[false].

@examples[#:eval curnel-eval
          (if true false true)
	  (elim Bool (λ (x : Bool) Bool) (false true) true)]
}

@defproc[(not [x Bool])
         Bool]{
Negates the boolean @racket[x].

@examples[#:eval curnel-eval
          (not true)
	  (not false)]
}

@defproc[(and [x Bool] [y Bool])
         Bool]{
The boolean @racket[and]. True if and only if @racket[x] and @racket[y] are both either @racket[true] or @racket[false].

@examples[#:eval curnel-eval
          (and true true)
	  (and false true)]
}

@defproc[(or [x Bool] [y Bool])
         Bool]{
The boolean @racket[or]. True if and only if either @racket[x] or @racket[y] is @racket[true].

@examples[#:eval curnel-eval
          (or true true)
	  (or false true)
	  (or false false)]
}

@defproc[(bool->meta-bool [syn syntax?]) boolean?]{
A meta-procedure, provided at phase 1, that converts syntax representing a
@racket[Bool] literal into a Racket (meta-level) @racket[boolean?].

@examples[#:eval curnel-eval
         (begin-for-syntax
           (displayln (bool->meta-bool #'true)))
]
}

@defproc[(meta-bool->bool [b boolean?]) syntax?]{
A meta-procedure, provided at phase 1, that converts a Racket (meta-level)
@racket[boolean?] into syntax representing a @racket[Bool].

@examples[#:eval curnel-eval
         (begin-for-syntax
           (displayln (meta-bool->bool #f)))
]
}