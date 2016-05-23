#lang scribble/base
@(require
  "defs.rkt"
  "bib.rkt")

@title*{Related Work}
Proof assistants remain an active area of study, but much of this work focuses
on aspects other than notation.

VeriML features a proof assistant with a small core over which the user can use
ML for writing extensions@~citea{stampoulis2010veriml}.
All extensions in VeriML are ML functions, and are therefore strongly
typed.
This enabled writing strongly typed tactics and decision procedures to
manipulate or generate proof terms.
Our work and the VeriML work would complement each other.
Extensions in VeriML are ML functions, so the user is limited to the notation of
function application but gets strongly typed extensions.
Our work enables advanced notation, but we do not consider the issue of
static guarantees for notation.
A language extensions system designed with a strongly typed language such as ML
would enable defining strongly typed notation.

@citeta{fisler1999implementing} study the linguistic issues related to
designing a "plug-and-play" theorem prover, in which users can select
a set of logics and interfaces that can be that can be easily
composed.
In their theorem prover, the users must write a plugin that is loaded
by the system.
While their focus is on extending the logics of the prover, each extensions can
define its own notation.
However, notations from one extension cannot be used within the notation from
another extension.

We ensure safe language extension by checking all code in the core language
after expansion.
This approach can result in type errors in expanded code that the user did not
write, if the extension author is not careful.
Alternative approaches ensure all type errors occur in the source language
rather than the expanded language.

@citeta{lorenzen:2016} demonstrates how to define well-typed extensions that
justify new typing rules in terms of the old type system.
Since each extension is well-typed, type checking happens in the extended
language rather than after expansion.
However, these extensions are currently limited to desugaring and do not enable
general purpose computation in a metalanguage.

@citeta{pombrio2015hygienic} develop techniques for @emph{resugaring}; rather
than catch errors before expanding extensions, these systems undo the expansion
before reporting errors.
Integrating this with a language-extension system could reduce the burden of
manually catching errors in new extensions.

The Milawa theorem prover@~citea{myreen2014reflective} allows the user to
redefine the proof-checking function, after establishing that the new proof
checker is valid.
The new proof checker may admit new syntax and new axioms can report errors in
terms of the extended proof language.
This enables sophisticated and safe extensions, and ensures type errors
occur in the surface language, but requires defining a new proof checker to
define macro expressible syntactic transformations.

While we focus on notation in this work, language extension also provides
support for meta-programming.
As we saw in @secref{sec:surface}, we can add support for using Cur as its
own dependently-typed staged meta-programming language @emph{without extending
the core language}.

Previous work on dependently-typed staged meta-programming in Idris required
extensions to the core language TT@~citea{brady2006}.
Similar work in Agda requires extending Agda with a set of
primitives@~citea{devriese2013}.
Neither work demonstrates the soundness of these extensions.

Later work on meta-programming in Idris adds the ability to quote
surface-language Idris, i.e. Idris code before elaboration@~citea{christiansen2014type}.
By starting from a language-extension system with quasiquotation and syntactic
macros, rather than adding quasiquotation to an existing elaborator, Cur
supports not only quasiquoting surface syntax, but quasiquoting any
user-defined extension to the surface syntax.

@(omit
"
Lots of related work regarding meta-programming:
Ott, Lem, binders unbound, making adhoc proof automation less adhoc,
ssreflect, autosubst, typed racket and languages as libraries.

3) Dependent Type Providers
   http://itu.dk/people/drc/pubs/dependent-type-providers.pdf

Practical implementation of a Dependently typed functional programming
language

http://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf

Proof of false in Coq 8.4pl5: https://github.com/clarus/falso

   Possible other related work
   http://link.springer.com/chapter/10.1007/3-540-44404-1_7

Related work regarding shrinking the trusted core:

   A small-core language, http://www.andres-loeh.de/PiSigma/PiSigma.pdf
   Attempts to shrink agdas core, http://www2.tcs.ifi.lmu.de/~abel/aim12.ma
   "
)
