#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label cur/stdlib/datum)
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/datum)"))

@title{Datum}
@defmodule[cur/stdlib/datum]
This library defines an interface for incrementally extending @racket[#%datum],
solving the problem of diamond inheritance for parsing library-defined data
literals.

@defform[(#%datum . syn)]{
A generic handler for Cur data literals.
Calls @racket[current-datum] to parse @racket[syn].
}

@defproc*[([(current-datum) (-> syntax-object? syntax-object?)]
           [(current-datum [p (-> syntax-object? procedure? syntax-object?)]) void?])]{
A phase 1 parameter, holding an open-recursive function for parsing data.
Setting @racket[current-datum] to a new procedure of the right interface
effectively extends the @racket[#%datum] parser.
Initially set to @racket[default-datum].

@;@examples[#:eval curnel-eval
@;(data Nat : 0 Type
@;  (z : Nat)
@;  (s : (-> Nat Nat)))
@;(define-for-syntax (nat->unary n)
@;  (if (zero? n)
@;      #`z
@;      #`(s #,(nat->unary (sub1 n)))))
@;(begin-for-syntax
@;  (current-datum (lambda (syn f)
@;                   (syntax-parse syn
@;                     [_:nat
@;                      (nat->unary (syntax->datum #'syn))]
@;                     [_ (f syn)]))))
@;0
@;]
}

@defproc[(default-datum [syn syntax?] [f procedure?]) syntax?]{
The default datum parser; raises an error, as it doesn't know how to parse anything.
}
