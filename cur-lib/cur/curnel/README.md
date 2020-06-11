# Curnel organization

The Curnel implements the core language of Cur. 
The Curnel is implemented as a series of languages, each extending the prior
language.
Each language implements some core typed forms for use in the surface language,
and pattern expanders for use in extending the language.

All extensions to the trusted core belong in this directory.

## coc.rkt
`coc.rkt` contains an implementation of the Calculus of Constructions (CoC) with
one impredicative universe and an infinite predicative hierarchy.

The impredicative universe is computationally and proof relevant, and thus
inconsistent with some classical axioms.
This is analogous to Coq's impredicative Set.

## coc-saccharata.rkt
`coc-saccharata.rkt` extends CoC with support for some syntactic sugar, such as
automatic currying.
This is necessarily in the core to implement inductive types in a reasonable way.

## cic-saccharata.rkt
`cic-saccharata.rkt` extends CoC Saccharata with indexed inductive type families.
This language essentially implements the Calculus of Inductive Constructions
(CIC), although there is a key difference. 
The implementation generates inductive types as type schemas, in the style of
Martin Löf type theory, rather than using a single eliminator and environment of
inductive declarations a la Coq.

## reflection.rkt
Implements a reflection API to give phase 1 access to the Cur type system for
language extension.
This is rapidly being replaced by Turnstile.

## lang.rkt
Implement the `#lang cur`. 
This language provides:
- `cic-saccharata.rkt` and the Racket (sub)module system at phase 0.
- `#lang racket`, `syntax/parse`, and the Curnel reflection API at phase 1.
