#lang scribble/manual
@require[@for-label[cur racket/base]]

@title{Cur}
@author{wilbowma (William J. Bowman @url{https://www.williamjbowman.com/})}

@defmodule[cur #:lang]

Cur is a simple dependently-typed language that arbitrary Racket meta-programs can manipulate. The
core logic of @racketmod[#:lang cur] is essentially UTT (@todo{citation needed}). The trusted core
provides nothing beyond this logic. However, Racket meta-programming provides features such as
modules, top-level definitions, multi-arity functions, implicit partial application, syntax notations,
a tactic DSL, interactive tactics, and a programming language meta-theory DSL. All these features are
provided by user-land code

Arbitrary @racketmod[racket] code can run at @tech{phases} higher than 0, but @racketmod[racket] code at
@tech{phase} 0 is unsupported and should result in an error. The language @racket[#:lang cur] exports
everything in @racketmod[racket], @racketmod[racket/syntax], and @racketmod[syntax/parse] at
@tech{phase} 1.

Cur provides reflection features to enables more advanced meta-programming. Cur exports Racket
functions at @tech{phase} 1 for type checking Cur terms, performing naïve type inference on Cur terms,
deciding equivalence between Cur terms, expanding macros in Cur terms, and evaluating Cur terms at
compile-time. Programmers can use these reflection feature with little fear, as the resulting
@tech{phase} 0 terms will always be type-checked again.
