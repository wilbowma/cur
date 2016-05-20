#lang scribble/base
@(require
  scribble/manual
  "defs.rkt")

Sophisticated domain-specific and user-defined notation is widely used in
formal models, but is poorly supported by proof assistants.
Many proof assistants support simple notation definitions, but no proof
assistant enables users to @emph{conveniently} define @emph{sophisticated}
notation.
For instance, in modeling a programming language, we often define infix
relations such as @code{Γ ⊢ e : t} and use BNF notation to specify the syntax
of the language.
In a proof assistant like Coq or Agda, users can easily define the notation
for @code{Γ ⊢ e : t}, but to use BNF notation the user must use a preprocessing
tool external to the proof assistant, which is cumbersome.

To support sophisticated user-defined notation, we propose to use
@emph{language extension} as a fundamental part of the design of a proof
assistant.
We describe how to design a language-extension systems that support safe,
convenient, and sophisticated user-defined extensions, and how to design a
proof assistant based on language extension.
We evaluate this design by building a proof assistant that features a small
dependent type theory as the core language and implementing the following
extensions in small user-defined libraries: pattern matching for inductive
types, dependently-typed staged meta-programming, a tactic-based proof
language, and BNF and inference-rule notation for inductive type definitions.