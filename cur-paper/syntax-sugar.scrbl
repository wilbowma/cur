#lang scribble/base
@(require
  scriblib/figure
  scriblib/footnote
  scribble/manual
  "defs.rkt"
  "bib.rkt"
  scribble-latex-utils/utils)

@title[#:tag "sec:surface"]{Growing a Surface Language}
Cur provides an object language with no more convenience than Curnel.
It contains only features necessary for expressivity and nothing that is macro
expressible in terms of other features@~citea{felleisen1990expressive}.
By contrast, Gallina, the core language of Coq, includes extensions that are
macro expressible in terms of other features, such as a non-dependent arrow
and multi-arity functions.

Let us now take on the role of a Cur user (more precisely, an extension author)
and begin implementing a surface language.
We begin by implementing the simple syntactic sugar like the non-dependent
arrow notation.
We then implement more sophisticated syntax sugar: we implement a @racket[let]
form with optional type annotations, and a pattern matching form for eliminating
inductive types.
We conclude with some extensions that go beyond syntax---extensions that add
compile-time behaviors but do not necessarily generate code, like debugging
features and staged meta-programming.

@section{Simple Syntax}
@exact{\vspace{-1.5em}}
@subsubsub*section*{Alias for @code{(Type 0)}}
Writing @code{(Type 0)} for all these examples is somewhat tedious.
We start with a simple example macro that elaborates @code{Type} to @code{(Type 0)}.
Eventually, a more sophisticated extension could resolve all universe levels
automatically, but this will do for now.
First, let us import a renamed copy of the default form:
@racketblock[
require
  only-in curnel
    Type default-Type
]
Next we define a simple macro with two syntaxes: one applied to an argument,
one without any argument.
In the first case, we simply expand to the default form.
In the second case, we provide level @racket[0] as a default.
Note that the choice of surface syntax does not affect how we write syntax
objects.

@racketblock[
define-syntax (Type syn)
  syntax-case syn ()
    [(Type i) #'(default-Type i)]
    [Type #'(default-Type 0)]
]

@exact{\vspace{-1.5em}}
@subsubsub*section*{Multi-Arity Syntax}
Cur provides only single-arity functions in the base language.
As mentioned in @secref{sec:cur}, we can redefine existing forms like function
and application syntax, so we redefine them to support multi-arity functions
via automatic currying.
First, let us import renamed copies of the default forms:
@racketblock[
require
  only-in curnel
    #%app default-app
    λ default-λ
]
With these renamed copies, we can redefine @racket[#%app] and @racket[λ] while
still generating code that uses the original forms.

Next, we define a simple recursive macro for @racket[λ] that curries all
arguments using @racket[default-λ].
@racketblock[
define-syntax λ
  syntax-rules (:)
    [(λ b) b]
    [(λ (a : t) (ar : tr) ... b)
     (default-λ (a : t) (λ (ar : tr) ... b))]

define-syntax lambda
  make-rename-transformer(#'λ)
]
The @racket[syntax-rules] form is similar to @racket[syntax-case], but
specialized to support writing simple syntactic rewrites rather than arbitrary
metalanguage computation.
The syntax @racket[...] is part of the pattern and template languages for syntax
objects.
In a pattern, it matches a list of the preceding pattern.
In a template, it splices in the list indicated by the preceding pattern.

Next, we redefine application.
The macro automatically curries applications using @racket[default-app].
@racketblock[
define-syntax #%app
  syntax-rules ()
    [(#%app e1 e2)
     (default-app e1 e2)]
    [(#%app e1 e2 e3 ...)
     (#%app (#%app e1 e2) e3 ...)]
]

These forms are automatically integrated into the object language, replacing
the old forms, and are ready to use even later in the same module:
@racketblock[
define id $ lambda (A : Type) (a : A) a
id Nat z
]
@exact{\vspace{-1.5em}}
@subsubsub*section*{Non-dependent Arrow Syntax}
Now let us define a non-dependent arrow form.
We start by defining a single-arity arrow syntax @racket[arrow]:
@RACKETBLOCK[
define-syntax (arrow syn)
  syntax-case syn ()
    [(arrow t1 t2)
     #`(Π (#,(gensym) : t1) t2)]
]
Note that in Cur we must explicitly generate a fresh name using
@racket[gensym], due to a limitation in the representation of names in our
object language.
We use syntax quasiquote @racket[#`code:blank] to create a syntax template that
supports escaping to compute parts of the template, and use syntax unquote
@RACKET[#,code:blank] to escape the template and run metalanguage expressions.

Now we can easily define the multi-arity arrow, with both ASCII and unicode
names.
@#reader scribble/comment-reader
(racketblock
define-syntax ->
  syntax-rules ()
    [(-> a) a]
    [(-> a a* ...)
     (arrow a (-> a* ...))]

define-syntax → make-rename-transformer(#'->)

;; Usage:
data Nat : Type
  z : Nat
  s : {Nat → Nat}
)

@subsubsub*section*{Top-level Function Definition Syntax}
Writing top-level function definitions using @racket[lambda] is verbose.
Most languages features special syntax for conveniently defining top-level
functions, so let us add this to Cur:
@racketblock[
define-syntax define
  syntax-rules (:)
    [(define (id (x : t) ...) body)
     (default-define id (lambda (x : t) ... body))]
    [(define id body)
     (default-define id body)]

define (id (A : Type) (a : A)) a
]

@subsubsub*section*{Notation for Formal Models and Proofs}
Recall that our original goal was to provide better support for user-defined
notation in formal models and proofs.
Thus far, we have merely defined a surface language, which users should not be
expected to do.
However, the same language-extension facilities serve both purposes.
As language implementers, we use language extension to build a surface language.
As users, we use language extension to define our own notation---and we have the
same power as language implementers when defining new notation.

For instance, suppose we as a user model the simply-typed λ-calculus.
After writing a small-step evaluation relation and a type-checking relation,
we want to use standard notation while doing proofs about the model.
We define this notation as follows:
@racketblock[
define-syntax-rule (↦ e1 e2) (steps-to e1 e2)

define-syntax ⊢
  syntax-rules (:)
    [(⊢ Γ e : t) (type-checks Γ e t)]

define-syntax nfx
  syntax-rules (⊢ :)
    [(nfx Γ ⊢ e : t) (⊢ Γ e : t)]
]
The form @racket[define-syntax-rule] is simply syntax sugar using
@racket[define-syntax] followed by @racket[syntax-rules].
The @code{nfx} macro is used by the sweet-expression reader to extend the
reader with new infix notation.
The reader can automatically parse some infix notation, but the
@code{type-checks} notation is irregular so we define the @code{nfx} macro to
assist the reader.

Now we can use the notation to state a lemma:
@racketblock[
define lemma:type-preservation
  (forall (e1 : STLC-Term) (e2 : STLC-Term)
          (Γ : STLC-Env) (t : STLC-Type)
    {{Γ ⊢ e1 : t} -> {e1 ↦ e2} -> {Γ ⊢ e2 : t}})
]
The sweet-expression reader provides some support for infix notation,
but other work has implemented more sophisticated support for non-s-expression
based syntax extensions.
@citeta{rafkind2012} used the extensible reader to implement syntax-extension for
algebraic notation.
Other work has even developed language-extension via syntactic macros based on
parsing expression grammars, rather than on pre-parsed s-expressions
representations@~citea{allen2009growing}.

@section{Sophisticated Syntax}
The extensions in the previous section are simple syntactic rewrites, but
recall that our goal is to support @emph{sophisticated} user-defined extensions.
The extensions we study in this section use metalanguage computation to compute
parts of the object language code.

@subsubsub*section*{Let Syntax}
Let us begin by defining @racket[let] in terms of application.
Note that a proper dependent @racket[let] requires changing the type system, so
this @racket[let] is only a programming convenience.
We define the @racket[let] construct with two syntaxes: one expects a
type annotation, while the other attempts to infer the type.
In the first syntax, when there is a type annotation, we manually type check
the annotated term before generating code so that we can report an error in the
surface syntax.
In the second syntax, when there is no annotation, we attempt to infer a type
and report an error if we cannot.
@RACKETBLOCK[
define-syntax (let syn)
  syntax-case syn (: =)
    [(let ([x = e : t]) body)
     (unless (cur-type-check? #'e #'t)
       (error 'let
         "~a does not have expected type ~a"
         #'e
         #'t)
     #'((λ (x : t) body) e))]
    [(let ([x = e]) body)
     (unless (cur-type-infer #'e)
       (error 'let
         "Could not infer type for ~a; ~a"
         #'e
         "try adding annotation via [x = e : t]")
     #`((λ (x : #,cur-type-infer(#'e)) body)
        e))]
]
Pattern variables are only bound inside syntax templates, so we use syntax
quote to refer @racket[e] and @racket[t] in metalanguage code.
The metalanguage function @code{error} takes a symbol naming the form in which
the error occurred, a format string where @code{~a} is a formatting escape, and
a list of arguments for the format string.
Syntax objects have associated source location information, so we could even
report error messages with the file name and line number of the @racket[let]
expression, but we omit this for clarity.

@subsubsub*section*{Pattern Matching Syntax}
@figure**["fig:match" "A Pattern Matcher for Inductive Types"
@#reader scribble/comment-reader #:escape-id UNSYNTAX
(RACKETBLOCK
define-syntax (match syn)
  syntax-case syn ()
    ; expects discriminant @racket[e] and list of clauses @racket[clause*]
    (_ e clause* ...)
     let* ([clauses (map clause-parse (syntax->list #'(clause* ...)))]
           [R (infer-result clauses)]
           [D (cur-type-infer #'e)]
           [motive #`(lambda (x : #,D) #,R)]
           [U (cur-type-infer R)])
       #`(elim #,D #,motive ()
            #,(map (curry clause->method D motive) clauses)
            e)

define-syntax (recur syn)
  syntax-case syn ()
    (_ id)
     dict-ref ih-dict $ syntax->datum #'id

begin-for-syntax
  define-struct clause (args body)
  define ih-dict (make-hash)

  define (clause-parse syn)
    syntax-case syn
      (pattern body)
       make-clause (syntax-case pattern (:)
                      [c '()]
                      [(c (x : t) ...) (syntax->list #'((x : t) ...))])
                    #'body

  define (infer-result clauses)
    for/or ([clause clauses])
      cur-type-infer $ clause-body clause

  define (infer-ihs D motive args-syn)
    syntax-case args-syn () ....

  ; D needed to detect recursive arguments
  ; motive needed to compute type of inductive hypotheses
  define (clause->method D motive clause)
    let* ([ihs (infer-ihs D motive (clause-args clause))])
      dict-for-each ihs
        lambda (k v)
          dict-set! ih-dict k $ car v
      #`(lambda
          #,@clause-args(clause)
          #,@(dict-map ihs (lambda (k v) #`(#,(car v) : #,(cdr v))))
          #,clause-body(clause))
)]
Recall the addition function for natural number we defined in
@secref{sec:curnel}, which we redefine as @racket[+] below:
@racketblock[
define (+ [n1 : Nat] [n2 : Nat])
  elim Nat
    lambda (x : Nat) Nat
    ()
    (n2
     lambda (x : Nat) (ih : Nat) $ s ih)
    n1
]

This version of @racket[+] is easier to read and write now that we have
multi-arity functions, but still requires a lot of annotations and other
syntactic overhead.
Instead, we would like to define @racket[plus] using pattern matching and
to avoid writing obvious annotations, like the motive, when they can be inferred.
We would like to define @racket[plus], for instance, like so:
@racketblock[
define (+ [n1 : Nat] [n2 : Nat])
  match n1
    z n2
    (s (x : Nat)) s $ recur x
]
In this definition we use @racket[match], which we present shortly.
The @racket[match] form automatically infers the motive, the annotations on
@racket[elim], and inductive hypotheses.
It also provides the @racket[recur] form to allows users to refer to generated
inductive hypotheses by the name of the recursive argument from which they are
derived.

@Figure-ref{fig:match} presents the definition of the @racket[match] extension.
This simplified version demonstrates how to coordinate two different
extensions, namely the @racket[match] and @racket[recur] forms, and how to
generate and compose multiple syntax templates.
It makes use of nontrivial metalanguage features, like state and user-defined
datatypes structures.
We omit parts of the implementation that do not contribute to the goal of
demonstrating these features, and features like error checking code.
Recall that @racket[...] is an identifier used in patterns and templates, so we
use @racket[....] to indicate omitted code.

First, we transform the syntax representing a sequence of clauses into a
list of syntax using @racket[syntax->list].
We parse each clause into a structure using @racket[clause-parse].
Each clauses consist of a pattern and a body.
The pattern must be either a constructor name for constructors that take no
arguments, or a constructor name followed by names with type annotations for
all arguments to the constructor.
We store the list of arguments and the body of the clause in a clause
structure, to be used when generating methods for the eliminator.

After parsing each clause, we compute the motive.
The body of the motive is the type @racket[R] of the
result of the @racket[match], and the argument to the motive has type
@racket[D] of the discriminant.
Note that in this implementation, we do not handle indexed inductive types.
The full implementation can infer some indexed inductive types and supports
optional annotation syntax for when inference fails.

Finally, we generate a method for each clause using @racket[clause->method].
While generating methods, we infer which arguments are recursive arguments and
compute the inductive hypotheses.
We update a compile-time dictionary @racket[ih-dict] that associates the
name of the recursive argument to the generated name for that inductive
hypothesis.
The @racket[recur] form looks up its argument in @racket[ih-dict].

@section{Beyond Syntax}
Thus far, all our examples demonstrate syntactic transformations.
Our sophisticated language-extension system also supports creating syntactic
forms that have semantic behavior at compile-time and do not necessarily
generate object language code.

For example, we can create a type assertion form that allows users to check
that an expression has a particular type and receive a type error if not:
@#reader scribble/comment-reader
(racketblock
define-syntax (:: syn)
  syntax-case syn ()
    (_ e t)
     if $ cur-type-check? #'e #'t
         #'(void)
         (error '::
           "Inferred ~a; expected ~a."
           #'t
           (cur-type-infer #'e))
; Usage:
{z :: Nat}
)
We check during expansion that @racket[e] has type @racket[t].
If the check succeeds, we generate the no-op expression @racket[#'(void)].
If the check fails, it reports an error similar to what we do for checking
annotations in the @racket[let] form.
This form has no behavior in the object language but provides extra
behavior at compile-time to support debugging.

We can also create a syntactic form that forces normalization at compile-time:
@racketblock[
define-syntax (run syn)
  syntax-case syn ()
    (_ expr) $ cur-normalize #'expr
]
The @racket[run] form does not provide new syntactic sugar, but transforms the
syntax by normalization via the reflection API.

This can be used to simplify proofs or perform staged meta-programming.
For example, we specialize the exponentiation function @racket[exp] to the
@racket[square] function at compile-time:
@racketblock[
define square $ run $ exp (s (s z))
]