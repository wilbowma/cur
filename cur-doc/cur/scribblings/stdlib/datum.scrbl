#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label cur/stdlib/datum)
  (for-label (only-in racket void? syntax? procedure? -> require only-in for-syntax begin-for-syntax lambda syntax->datum))
  (for-label (only-in syntax/parse syntax-parse))
  (for-label (only-in (only-meta-in 1 cur/stdlib/nat) nat->unary))
  (for-label (only-in (only-meta-in 0 cur/stdlib/nat) z))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/datum) (require cur/stdlib/sugar)"))

@title{Datum}
@defmodule[cur/stdlib/datum]
This library defines an interface for incrementally extending @racket[#%datum],
solving the problem of diamond inheritance for parsing library-defined data
literals.

@defform[(#%datum . syn)]{
A generic handler for Cur data literals.
Calls @racket[current-datum] to parse @racket[syn].
}

@defproc*[([(current-datum) (-> syntax? syntax?)]
           [(current-datum [p (-> syntax? procedure? syntax?)]) void?])]{
A phase 1 parameter, holding an open-recursive function for parsing data.
Setting @racket[current-datum] to a new procedure of the right interface
effectively extends the @racket[#%datum] parser.
Initially set to @racket[default-datum].

@examples[#:eval curnel-eval
0
(require cur/stdlib/nat)
(begin-for-syntax
  (current-datum (lambda (syn f)
                   (syntax-parse syn
                     [e:nat
                      (nat->unary (syntax->datum syn))]
                     (code:comment "User must manually call f if parsing fails.")
                     [_ (f syn)]))))
0
]
}

@defproc[(default-datum [syn syntax?] [f procedure?]) syntax?]{
The default datum parser; raises an error, as it doesn't know how to parse anything.
}
