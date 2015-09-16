#lang scribble/manual
@(require
   racket/function)

@(define (todo . args)
   (apply margin-note* "TODO: " args))

@(define (gtech x)
   (tech x #:doc '(lib "scribblings/guide/guide.scrbl")))

@title{Cur}
@author[@author+email["William J. Bowman" "wjb@williamjbowman.com"]]

@defmodule[cur #:lang]

The language @racketmodname[cur] is a dependently-typed language that arbitrary Racket meta-programs
can manipulate.
The core language of @racketmodname[cur] is essentially TT@todo{citation
e.g. https://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf chapter 2}.
The trusted core provides nothing beyond this language.
However, untrusted user-land code provides, via Racket meta-programming, features such as modules, top-level
definitions, multi-arity functions, implicit partial application, syntax notations, a tactic DSL,
interactive tactics, and a programming language meta-theory DSL.
These features run at compile time and generate @tech{curnel forms}, forms in the core language,
which are type-checked before they are run.

Arbitrary @racketmodname[racket] code can run at @gtech{phases} higher than 0, but
@racketmodname[racket] code at @gtech{phase} 0 is unsupported and should result in a syntax error.
The language @racketmodname[cur] exports everything in @racketmodname[racket],
@racketmodname[racket/syntax], and @racketmodname[syntax/parse] at @gtech{phase} 1.

The language @racketmodname[cur] provides reflection features to equip users with the tools necessary
to write advanced meta-programs.
These features in includes compile-time functions for type-checking, performing naïve type inference,
deciding equivalence between @racketmodname[cur] terms, expanding macros in @racketmodname[cur] forms,
and evaluating @racketmodname[cur] forms at compile-time.
Programmers can use these reflection feature with little fear, as the resulting @tech{curnel forms}
will always be type-checked prior to running.

@table-of-contents[]

@section{Curnel Forms}
@deftech{Curnel forms} are the core forms provided @racketmodname[cur].
These form come directly from the trusted core and are all that remain at @gtech{runtime}.
The core of @racketmodname[cur] is essentially TT.
For a very understandable in-depth look at TT, see chapter 2 of
@hyperlink["https://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf"
           "Practical Implementation of a Dependently Typed Functional Programming Language"], by
Edwin C. Brady.

@(require racket/sandbox scribble/eval)
@(define curnel-eval
   (parameterize ([sandbox-output 'string]
                  [sandbox-error-output 'string]
                  [sandbox-memory-limit 500])
     (make-module-evaluator "#lang cur")))


@;(require (for-label cur/curnel/redex-lang))
@defform*[((lambda (id : type-expr) body-expr)
           (λ (id : type-expr) body-expr))]{
Produces a single arity procedure, binding the identifier id in body-expr and in the type of
body-expr.
Both type-expr and body-expr can contain non-curnel forms, such as macros.}
@examples[#:eval curnel-eval
          (lambda (x : Type) x)
          (lambda (x : Type) x)]

@examples[#:eval curnel-eval
          (define-syntax-rule (computed-type _) Type)
          (lambda (x : (computed-type bool)) x)
          (lambda (x : Type) x)]

@examples[#:eval curnel-eval
          (lambda (a : Type) (lambda (x : a) x))]

@section{Reflection Forms}
