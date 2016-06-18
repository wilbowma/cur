#lang scribble/base
@(require
  scribble/manual
  scriblib/footnote
  "defs.rkt"
  "bib.rkt")

@title*{Introduction}
Notation is important to convey ideas quickly while ignoring uninteresting
details, but notation is not fixed.
Each domain has its own notation used to hide the uninteresting details common
in that domain.
The notation commonly used in programming languages research differs from the
notation commonly used in cryptography.
Even in the same domain, individual results require new notation to suit the
needs of each new model or proof.
Every new programming languages result may use common domain-specific notation,
like BNF grammars, but may also define new notation to convey new ideas.

Notation is a way of @emph{informally} extending a @emph{formal} model.
When working with models on papers, we may conveniently create arbitrarily
sophisticated notation.
We may define simple syntactic sugar by saying "we write @code{let x = e1 in
e2} to mean @code{(λ x : t. e1) e2}".
Or we may define sophisticated extensions that require the reader to perform
computation: "we omit the type annotation and instead write @code{λ x. e} when
the type of @code{x} can be inferred".

Creating these extensions is easy when developing models on paper, but not when
using proof assistants.
Proof assistants provide increased confidence in formal models and proofs, but
lack support for allowing users to @emph{conveniently} define
@emph{sophisticated} extensions.
This lack of support has two downsides.
First, formal models need to be reproduced in another medium (such as LaTeX) to
communicate them effectively, which duplicates effort and risks the two models
falling out of sync.
Second, it decreases confidence that the specification is correct since the
model must be manually encoded into the language of the proof assistant, rather
than written in familiar notation.

Some proof assistants, like Agda, enable convenient user-defined extensions as
long as the extension is not sophisticated.
Agda's mixfix notation@~citea{danielsson2011parsing} is convenient to use but
only supports simple notation definitions, like writing a function named
@code{_ ⊢ _ : _}, where @code{_} indicates the position of arguments.
Other proof assistants, like Coq, support sophisticated extensions, but
creating these extensions is inconvenient to the point that few users can do it.
Writing a Coq plugin requires the developer to use a separate toolchain to
compile against the Coq implementation, and requires the user to compile and
link the plugin against their Coq installation.
However, these plugins support sophisticated extensions like
Mtac@~citea{ziliani2013mtac}, a new tactic language for Coq.

To provide support convenience and sophisticated user-defined extension, we
propose to design proof assistants by using language extension as a fundamental
feature.
Informally, we can think of this design as follows: rather than start
with a proof assistant and add user-defined extensions, we start with a core
language plus a language-extension system from which we can "grow" a proof
assistant.
We explain the design in detail by:
@itemlist[
  @item{Describing a core language for expressing formal models and proofs
  (@secref{sec:curnel}).
  Our core language, called Curnel, is a dependently typed λ-calculus, and
  does not contain any features except those required for expressing
  @emph{encodings} of formal models and proofs.
  The Curnel implementation is less than 700 lines of code.}

  @item{Describing the design and implementation of our language-extension
  system (@secref{sec:cur}).
  We explain what it means for language-extension systems to enable safe,
  convenient, and sophisticated extensions, and how to build the "seed" of a
  proof assistant from a core language and a language-extension system.}
]
We evaluate this design by implementing a proof assistant called Cur that
supports safe, convenient, and sophisticated language extension as defined
in @secref{sec:cur}.
To evaluate convenience, we rely partially on lines of code as a proxy,
although it does not take into account automatic integration into the proof
assistant.
To evaluate the level of sophistication we support, we implement
proof-of-concept versions of features provided by existing proof assistants and
one feature that is only supported via external tools.
Specifically, we demonstrate that Cur:
@itemlist[
  @item{Enables users to define syntactic sugar and surface language features
  that are primitive in the surface languages of other proof assistants
  (@secref{sec:surface}).
  We build a proof assistant by implementing a surface language as a
  user-defined library.
  This library provides notation including @code{let}, non-dependent function
  arrows, automatic currying, pattern matching on inductive types, and
  dependently-typed staged meta-programming.
  This library is less than 400 lines of code.}

  @item{Enables users to define tactic languages for writing proofs, including
  interactive tactic-based proving (@secref{sec:tactics}).
  While existing proof assistants like Coq and
  VeriML@~citea{stampoulis2010veriml} provide tactic languages, they either do
  not support user-defined tactic languages, or require users to use external
  toolchains.
  Our design enables writing the tactic language in a library, using the same
  extension system that provides syntactic sugar.
  Our implementation of this tactic system, excluding tactics, is less than 200
  lines of code.
  By comparison, the Mtac plugin for Coq is over 1200 lines of code.}

  @item{Enables users to define domain-specific languages for writing formal
  models (@secref{sec:olly}).
  In particular, we define a library that enables modeling programming
  languages using BNF and inference rule notation, and extracting the models to
  Coq and LaTeX in addition to using them in Cur directly.
  This library is inspired by Ott@~citea{sewell:2007}, an external tool that
  outputs files for multiple proof assistants from a single file with BNF and
  inference rule notation.
  While Ott is a mature tools with many more feature so comparing directly
  is difficult, our library is less than 400 lines of code, while just the
  lexer for Ott is more than 400 lines of code.
  No other proof assistant supports BNF and inference-rule notation in the
  language, nor provides support for users to add the feature as a library in
  just 400 lines of code.}
]