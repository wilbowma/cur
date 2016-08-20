#lang scribble/base
@(require
  scribble/manual
  "defs.rkt")

Theoreticians often use sophisticated notation to communicate and reason about
key ideas in their theories and models.
Notation is often domain-specific or even invented on-the-fly when creating a
new theory or model.
Proof assistants aid theoreticians by rigorously checking formal models, but
have poor support for allowing users to @emph{conveniently} define and use
@emph{sophisticated} notation.
For example, in a proof assistant like Coq or Agda, users can easily define
simple notation like @code{Γ ⊢ e : t}, but to use BNF notation the user must use
a preprocessing tool external to the proof assistant, which is cumbersome.

To support convenient and sophisticated extension, we can use @emph{language
extension} as a fundamental part of the design of a proof assistant.
By starting from language extension we can not only facilitate convenient and
sophisticated user-defined extensions, but also get a single, compositional
system for writing all extensions to the core proof language.

We describe how to design a language-extension system that supports safe,
convenient, and sophisticated user-defined extensions, and how to design a
proof assistant based on language extension.
We evaluate this design by building a proof assistant that features a small
dependent type theory as the core language and implementing the following
extensions in small user-defined libraries: pattern matching for inductive
types, dependently typed staged meta-programming, a tactic language, and BNF
and inference-rule notation for inductive type definitions.