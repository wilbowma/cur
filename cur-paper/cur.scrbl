#lang scribble/base
@(require
  "defs.rkt"
  "bib.rkt"
  "cur.rkt"
  scribble/manual
  scriblib/footnote
  scriblib/figure)

@title[#:tag "sec:cur"]{Designing for Language Extension}
If we were following the design of other proof assistants, we would now
describe a practical surface language.
The surface language would include features that are not necessary for
expressivity but simplify development.
We would then write an elaborator that transforms the surface language into the
core language.
In this paper, we instead essentially develop an expressive and extensible
elaborator and expose it to the user.
This elaborator is the language-extension system.

As with our choice of core language, the choice of language-extension system is
not vital to our design.
We choose Racket's language-extension system as it is the subject of active
research and development and already supports convenient and sophisticated
extension, so we need only ensure the extensions are safe.
We imagine that if a proof assistant like Coq were implemented using our
design, it would feature a language-extension system written in OCaml.
Whatever the choice, we want the language-extension system to enable the users
to conveniently write safe and sophisticated extensions.

We will refer to the "metalanguage" as the language in which users write
extensions and the "object language" as the language in which users write proof
and formal models.
In fact, Cur supports an infinite hierarchy of metalanguages; we do not discuss
this further in this paper, but refer the interested reader to the literature
on multi-stage programming---@citeta{taha2004gentle}, for example.

@subsubsub*section*{Safe Extension}
For extensions to be @emph{safe} in the context of a proof assistant, all
extensions must be valid---in the sense that they do not introduce
inconsistency---according to the core language.
The simplest and most convenient way to ensure safety is to check the
output of all extensions after elaboration into the core language.
The biggest drawback to this approach is that type errors may arise in expanded
code, rather than in the code written by the user.

To improve type errors, we enable extension authors to check subforms and
report errors during expansion.
While our design enables extension authors to overcome the problem, other
approaches avoid the problem entirely by typing extensions.
We discuss these alternatives in @secref{sec:related}.

@subsubsub*section*{Convenient Extension}
To ensure extensions are @emph{convenient} to write, we must allow extension
authors to reuse language infrastructure and automatically integrate extensions
into the object language.
Extension authors should not need separate toolchains to write or integrate new
extensions; the language-extension system should be an integral part of the
proof assistant.
Users should be free to write metalanguage and object language code in the same
module.
@;The user should not need to manually deal with parsing object language code.
Users should only need to write the semantics of extension; the extensions
should automatically integrate into the parser and receive parsed objects to
compute over.
All extensions should be automatically checked for safety.

By comparison, Coq plugins require users to compile against the Coq
implementation using a separate toolchain.
Users abandon their project when they find they require a plugin.@note{There are
many examples on the Coq-Club mailing list.}

Writing extensions as external preprocessors, such as Ott@~citea{sewell:2007},
requires users to write a parser and compiler, and the resulting tool does not
integrate into the object language.
This adds a barrier to both developing and using such extensions.

@subsubsub*section*{Sophisticated Extension}
To support @emph{sophisticated} extension, we must allow extensions to perform
computation in a general-purpose metalanguage.
New extensions should integrate into the syntax of the object language as
if they were native syntax.
Users must be able to redefine and extend existing syntax, including base
syntax like @racket[λ] and application.

Language-extension should also support extensions to non-syntactic features of the language.
A user may want to extend the reader to parse new literals, rather than just
perform rewrites on the AST of the object language.
A user may want to extend the interpretation of a module to perform advanced
type inference before the existing type checker runs.

Mixfix notation in Agda only supports defining new functions whose arguments
appear in non-standard positions.
It does not support defining a form whose subforms are not evaluated as object
language expressions; we give an example of such a form in @secref{sec:olly}.

Coq features notations and Idris@~citea{idris:jfp} features macros, but these
are limited to simple syntactic rewrites.
They do not support general-purpose computation nor redefining existing syntax.

@section[#:tag "sec:cur:lang"]{Racket Languages and Language Extension}
To describe how we implement Cur and language extension in Cur, we must first
explain Racket's language-extension facilities.
Racket is both a language and a system for defining
languages@~citea{samth:2011}.
We use Racket as both: we implement Cur as an object language in Racket as a
system, and write language extensions in Cur using Racket as the metalanguage.
We use Racket because Racket's existing language extension features support
convenient and sophisticated extensions as defined earlier in the section.
We describe how we enforce safety later in this section.

Each Racket library provides a set of definitions that includes both syntactic
forms such as @racket[lambda] or @racket[define] and values such as
@racket[Nat] or @racket[plus].
Roughly speaking, definitions exist in one of two phases: compile-time and
run-time.
Compile-time definitions include both syntactic forms and value definitions.
Run-time definitions include only value definitions.
Compile-time definitions are written in a metalanguage, while run-time
definitions are written in an object language.
Defining new syntactic forms extends the object language.
In Racket (the language), the metalanguage and object language are the same.
In Cur, we create a new object language but leave Racket as metalanguage.

We define syntactic forms using syntactic macros.
Each macro binds an identifier to a @emph{transformer}, a metalanguage function
on @emph{syntax objects}---a data type representing object language syntax.
For example, if we assume the object language contains the form @racket[λ], we
can define a new ASCII version @racket[lambda] as follows:
@#reader scribble/comment-reader
(racketblock
;; Start a metalanguage block
(begin-for-syntax
  ;; A metalanguage function definition
  (define (transform-lambda syn)
    ;; Expect ":" to be a literal symbol
    (syntax-case syn (:)
      [(_ (x : t) e)
      #'(λ (x : t) e)])))

;; Defines an object language "lambda" form
(define-syntax lambda transform-lambda)
)
The form @code{begin-for-syntax} starts a metalanguage block; it can contain
arbitrary Racket definitions that will only be visible at compile-time.

The transformer function @racket[transform-lambda] uses @code{syntax-case} to
pattern match on the syntax object.
It also takes a set of literals.
This set, @racket[(:)], declares that @racket[:] should be treated as a
literal and not as a pattern variable.
Where @code{_} appears in a pattern, we do not bind a pattern variable.

In @racket[transform-lambda], we ignore the first element of the syntax, as
that will be the name of the macro.
In the body of the clause, we use syntax quote @racket[#'code:blank] to create
a template for a new syntax object.
Pattern variables are bound inside the template.
We simply preserve the pattern of the syntax object, and replace the macro
identifier with the unicode name @racket[λ].
In a practical implementation, we would add additional conditions on the
pattern variables, such as check that @code{x} is an identifier rather than an
arbitrary expression.

Finally, outside the meta-language block, we declare the new syntactic form
using @racket[define-syntax], and it is added to the object language.

The first stage of running a program is to run the macro expander.
The expander recursively traverses the syntax and calls the associated
transformer when it reaches a use of a macro identifier.
This recursive expansion enables macros to generate calls to other macros, and
to build abstractions for defining macros.

In Racket, we can even use macros to extend and redefine language features that
do not normally have an associated syntactic identifier, like the semantics of
application.
Language features that do not normally have an associated identifier have a
secondary explicit name.
For example, while we normally write application @racket[(f e)], this is just a
special syntax for @racket[(#%app f e)].
We can redefine application by redefining @racket[#%app], exactly as we defined
@racket[lambda].
Similarly, we can redefine the semantics of a module by redefining the
@racket[#%module-begin] form.
The ability to redefine language features enables the most sophisticated
language extensions and allows us to define new object languages in Racket.

We define a new language by defining a library that provides the base syntactic
forms of the language and a definition for @racket[#%module-begin] to
implements the semantics of a module.
Each Racket module begins with a line of the form @racketmodfont{#lang name},
where @racketmodfont{name} is the name of a library.
This causes Racket to use the library @racketmodfont{name} to interpret the
module.

We can also define extensions to the language reader which allow adding new
literals or entirely new kinds of syntax for writing object and metalanguage
programs.
A reader mixin is an extension to the reader.
Users can use reader mixins by adding them before the language name in the
@racketmodfont{#lang name} line.
For example, @code{#lang sweet-exp cur} adds the sweet-expression reader
@code{sweet-exp} to Cur, allowing users to write Cur using sweet-expressions
instead of Racket's usual s-expressions.
Using reader mixins does not affect how macros are written, since macros are
defined on syntax objects which the reader returns, and not on, say, token streams.

@section{Implementing Cur}
We define Cur as a Racket language invoked using @code{#lang cur}.
Cur uses Racket as the metalanguage, but replaces the object language.
The base syntactic forms of Cur are the Curnel forms given @secref{sec:curnel}.
For example, we can write the identity function as:
@codeblock{
#lang cur

(λ (A : (Type 0)) (λ (a : A) a))

((id Nat) z)

; Explicitly use the application form
(#%app (#%app id Nat) z)
}
Cur also provides a @racket[define] form for creating run-time value
definitions and a @racket[data] form for defining inductive types:
@racketblock[
(define id (λ (A : (Type 0)) (λ (a : A) a)))

(data Nat
  (z : Nat)
  (s : (Π (x : Nat) Nat)))
]
The base forms plus @racket[define] and @racket[data] make up the default
object language.
The module semantics recursively expand all syntactic forms into base forms.
The forms @racket[data] and @racket[define] generate no code, but affect the
module's environment.
The @racket[data] form extends the module's inductive type declaration
@render-term[Δ].
The @racket[define] form extends the module's value definitions.
As each syntactic form in the module is expanded, prior value definitions are
inlined and added to the term environment @render-term[Γ], the expanded term is
type-checked, and top-level expression are normalized and printed.

We can write macros as we saw in the previous section to extend the syntax of
Cur.
The example of the ASCII @racket[lambda] is a valid Cur extension.
As in Racket, we can also build and use metalanguage abstractions to simplify
defining new language extensions.
For instance, the previous example required a lot of code to simply add another
name to an existing form.
Instead, we could use the following metalanguage abstraction that generate
transformers that just replace the macro identifier with another identifier:
@codeblock{
(define-syntax lambda
  (make-rename-transformer #'λ))

; id, now without unicode
(define id
  (lambda (A : (Type 0)) (lambda (a : A) a)))
}

@section{Reflection API}
Some of the extensions we want to write check and infer types, and run Cur
terms at compile-time.  We can implement staged meta-programming by running Cur
terms at compile-time.
We can add type errors to extensions by type-checking during macro expansion.
We therefore provide a @emph{reflection API}---a metalanguage API to the Curnel
implementation---for language extensions to use.
We explain the API functions that we use in the rest of this paper.
Note that these API functions are added to the metalanguage, not the object
language, and can only be used by extensions during expansion and before object
language code is checked in the core language.

@(declare-exporting cur/curnel/redex-lang)
@defproc[(cur-expand [syn SyntaxObject] [id Identifier] ...) SyntaxObject]{
The @racket[cur-expand] function runs the macro expander on @racket[syn] until
the expander encounters a base form or one of the identifiers in the @racket[id
...] list.
The resulting term is not a fully expanded Curnel term; expansion halts when
the top-level form begins with any of the identifiers in the @racket[id] list
or any of the Curnel base forms.
For instance, @racket[(cur-expand #'(λ (x : t) e))] does not expand @racket[t]
or @racket[e] since @racket[λ] is a base form.
This function lets users write extensions by only considering certain syntactic
forms.
Since users can arbitrarily extend the syntax of Cur, using @racket[cur-expand]
before pattern matching in a new extensions ensures all unexpected extensions
are already expanded.
}

@defproc[(cur-type-check? [term SyntaxObject] [type SyntaxObject]) Boolean]{
The @racket[cur-type-check?] function returns @racket[true] when @racket[term]
expands to @render-term[e], @racket[type] expands to @render-term[t], and
@render-term[(type-check Δ Γ e t)] holds, and returns @racket[false] otherwise.
Note that this function is not meant to provide an error message; it is meant
to be used by extensions that catch type errors in surface syntax and provide
their own error messages.
}

@defproc[(cur-type-infer [term SyntaxObject]) (Maybe SyntaxObject)]{
The @racket[cur-type-infer] function returns a syntax representation of
@render-term[t] when @racket[term] expands to the term @render-term[e] and
@render-term[(type-infer Δ Γ e t)] holds, and @racket[false] otherwise.
This function allows users to build type inference into extensions and reduce
annotation burden.
}

@defproc[(cur-normalize [term SyntaxObject]) SyntaxObject]{
The @racket[cur-normalize] function is Cur's version of @racket[eval], but
usable only by extensions at compile-time.
It essentially calls the implementation of module semantics explained earlier:
it expands all extensions, type checks the result, then normalizes the term in
the Curnel.
Specifically, the function returns a syntax representation of @render-term[e_1]
when @racket[term] expands to a well-typed term @render-term[e_0] and
@render-term[e_1] = @render-term[(reduce Δ e_0)].
This lets users explicitly reduce terms or simplify proofs when the
type system or other extensions might not evaluate far enough.

This is similar to a feature in Zombie@~citea{weirich2013combining}; Zombie
users can write potentially non-terminating program to compute proofs, but to
do so must explicitly force evaluation and thus act as a termination oracle.
As Cur is terminating, the similarity is fleeting.

This function also enables us to implement staged meta-programming and run-time
reflection without extending the core language.
}