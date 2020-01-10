#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label cur/stdlib/datum)
  (for-label (only-meta-in 0 cur/stdlib/list))
  (for-label (only-meta-in 0 cur/stdlib/ascii))
  (for-label (only-meta-in 0 cur/stdlib/bool))
  (for-label cur/stdlib/sugar)
  (for-label (only-in racket syntax? or/c string? char? procedure?))
  (for-label cur/stdlib/racket-ascii)
  scribble/eval)

@(define curnel-eval
   (curnel-sandbox "(require cur/stdlib/bool cur/stdlib/list cur/stdlib/ascii cur/stdlib/sugar)"))

@title{ASCII}
@defmodule[cur/stdlib/ascii]
This library defines ASCII characters and strings, and a @racket[#%datum]
extension for ASCII string literals.

@deftogether[(@defthing[#:kind "0 parameter type" Ascii Type]
              @defthing[#:kind "constructor" ascii (-> Bool Bool Bool Bool Bool Bool Bool Ascii)])]{
A datatype representing an ASCII character, as a bit vector.

@examples[#:eval curnel-eval
          (define zero (ascii false false false false false false false))
          (define one (ascii false false false false false false true))
          ""
          "1"
]
}

@defthing[#:kind "type" Ascii-Str Type]{
The type of ASCII string; equivalent to @racket[(List Ascii)].
}

@defthing[#:kind "type" empty-ascii-str Ascii-Str]{
The empty string; equivalent to @racket[(nil Ascii)] and @racket[""].
}

@defproc[(ascii-str-concat [str1 Ascii-Str] [str2 Ascii-Str]) Ascii-Str]{
Concatenates two strings, appending @racket[str2] to the end of @racket[str1].
}

@defproc[(ascii-str-length [str Ascii-Str]) Nat]{
Returns the length of the string @racket[str].
}

@defproc[(meta-ascii->ascii [syn (or/c syntax? #f)] [char ascii-char?]) syntax?]{
A meta-procedure, provided at phase 1, for converting a Racket (meta-level)
@racket[ascii-char?] into syntax representing an @racket[Ascii]. If @racket[syn]
is provided, it is used in error messages in the even that @racket[char] is not
an @racket[ascii-char?].
}

@defproc[(meta-string->ascii-str [syn (or/c syntax? #f)] [str ascii-string?]) syntax?]{
A meta-procedure, provided at phase 1, for converting a Racket (meta-level)
@racket[ascii-string?] into syntax representing an @racket[Ascii-Str].
If @racket[syn] is provided, it is used in error messages in the even that
@racket[str] is not an @racket[ascii-string?].
}

@defproc[(ascii-datum [syn syntax?] [f procedure?]) syntax?]{
A meta-procedure, provided at phase 1, for parsing ASCII string literals.
This module automatically updates @racket[#%datum] using this procedure.

@examples[#:eval curnel-eval
          ""
          "1"]
}

@defproc[(ascii->meta-ascii [syn syntax?]) ascii-char?]{
A meta-procedure, provided at phase 1, for converting syntax representing a
@racket[Ascii] literal into a Racket (meta-level) @racket[ascii-char?].
}

@defproc[(ascii-str->meta-string [syn syntax?]) ascii-string?]{
A meta-procedure, provided at phase 1, for converting syntax representing a
@racket[Ascii-Str] literal into a Racket (meta-level) @racket[ascii-string?].
}