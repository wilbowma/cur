#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label racket/base data/bit-vector cur/stdlib/racket-ascii)
  scribble/eval)

@title{Racket ASCII}
@defmodule[cur/stdlib/racket-ascii]
This library defines Racket tools for manipulating ASCII string.
It will eventually be moved out of Cur; do not rely on it.

@defproc[(ascii-char? [c char?]) boolean?]{
Returns @racket[#t] when @racket[c] is valid as a 7-bit ASCII character, and @racket[#f] otherwise.
}

@defproc[(ascii-string? [str string?]) boolean?]{
Returns @racket[#t] when @racket[str] contains only characters that are valid as
a 7-bit ASCII character, and @racket[#f] otherwise.
}

@defproc[(byte->ascii-bit-vector [b byte?]) bit-vector?]{
Converts @racket[b] into a @racket[bit-vector] of a length 7, interpreted as a
ASCII character; the sign bit of @racket[b] is ignored.
}

@defproc[(ascii-bit-vector->byte [bv bit-vector?]) byte?]{
Converts a @racket[bv] of length 7, interpreted as an ASCII character, into a
@racket[byte].
}