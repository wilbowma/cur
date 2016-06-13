#lang scribble/sigplan @preprint @nocopyright
@(require
  scribble/manual
  scriblib/footnote
  "defs.rkt"
  "bib.rkt")

@title{Growing a Proof Assistant}
@(authorinfo "William J. Bowman" "wjb@williamjbowman.com" "Northeastern University")

@; copy-paste from abstract
@abstract{
Sophisticated domain-specific and user-defined notation is widely used in
formal models, but is poorly supported by proof assistants.
This notation provides informal extensions to formal model that aid in
communicating and reasoning about key ideas.
Unfortunately, proof assistants do not allows users to @emph{conveniently}
define @emph{sophisticated} notation.
For instance, in modeling a programming language, we often define infix
relations such as @code{Γ ⊢ e : t} and use BNF notation to specify the syntax
of the language.
In a proof assistant like Coq or Agda, users can easily define the notation
for @code{Γ ⊢ e : t}, but to use BNF notation the user must use a preprocessing
tool external to the proof assistant, which is cumbersome.

To support sophisticated user-defined notation, we propose to use
@emph{language extension} as a fundamental part of the design of a proof
assistant.
We describe how to design a language-extension system that support safe,
convenient, and sophisticated user-defined extensions, and how to design a
proof assistant based on language extension.
}

@;Copy-pasta from intro
@section*{Introduction}
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

In this talk, we describe Cur, a prototype proof assistant and
dependently-typed programming language built using this design, and describe
sophisticated extensions that are simple to write due to this design.
We start by describing Curnel, a pure, dependently typed λ-calculus sufficient
for encoding formal models and proofs.
Then we describe how we add a language-extension system to build Cur.

Cur uses Racket, an effectful, functional language, as a meta-language.
Racket macros can be used to extend the syntax of Cur, providing new notation.
Furthermore, since Racket macros can perform arbitrary compile-time
computation, macros provide a hook for sophisticated extensions such as type
inference, staged computation, embedded DSLs, program extraction, and solvers.
We describe several such extensions built in Cur.

@(generate-bibliography)