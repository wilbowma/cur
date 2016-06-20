#lang scribble/base
@(require
  (only-in redex/reduction-semantics term)
  "defs.rkt"
  "cur.rkt"
  "bib.rkt"
  scribble/manual
  scriblib/figure
  racket/function
  racket/list)

@title[#:tag "sec:curnel"]{Core Language}
Our choice of core language is not vital to our design.
We choose a dependently-typed calculus because dependent types have proven to
be useful not only for theorem proving but also for verified programming.
Whatever the choice, we want to restrict the core language to contain only
features necessary to represent the models, proofs, and programs that we are
interested in.
Features that are not required for
@emph{expressivity}@~citea{felleisen1990expressive}, that only add convenience or
reduce burden for the user, should be implemented using language extension.

Our core language, Curnel, is a dependently-typed λ-calculus with inductive
families@~citea{dybjer:1994}, an infinite hierarchy of cumulative predicative
universes, and an impredicative universe.
Curnel is inspired by TT, the core language of Idris@~citea{idris:jfp}, and
similar to Luo's UTT@~citea{luo1994computation}.
Curnel is implemented in Redex@~citea["matthews2004visual"
"felleisen2009semantics"] and all figures in this section are extracted from
the Redex implementation, so some notation may be slightly non-standard.
@figure["fig:curnel-syntax" "Curnel Syntax and Dynamic Semantics"
@verbatim|{
|@(render-language ttL)
|@(render-language tt-ctxtL)

|@(render-reduction-relation (tt--> (term ·)) #:style table-reduction-style)
}|
]

The top of @Figure-ref{fig:curnel-syntax} presents the syntax of Curnel.
A Curnel term is either a universe @render-term[U], a function
@render-term[(λ (x : t) e)], a variable, a dependent function type
@render-term[(Π (x : t) t)], an application @render-term[(e e)], or the
elimination of an inductive type @render-term[(elim D motive (indices ...) (methods ...) e)].
We write universes of level @render-term[i] as @render-term[(Unv i)].
We usually write variables using the meta-variable @render-term[x],
but we use @render-term[D] for the name of declared inductive types and
@render-term[c] for the names of inductive-type constructors.
We use application contexts @render-term[Θ] to represent nested application,
and @render-term[Ξ] to represent nested product contexts (telescopes).

The language is parameterized by a sequence of inductive-type
declarations @render-term[Δ].
The declaration @render-term[(Δ (D : t ((c : t_c) ...)))] extends
@render-term[Δ] with the inductive type @render-term[D] of type
@render-term[t] whose constructors are @render-term[(c ...)] with
types @render-term[(t_c ...)].
Inductive types in Curnel do not support @emph{parameters}, indices to
the inductive family that are invariant across the definition, and
must satisfy the strict positivity condition.

As an example of writing in Curnel, we can encode the natural numbers and write
the addition function as follows.
First we define the natural numbers:
@nested[#:style 'code-inset
  @render-term[(∅ (Nat : (Unv 0) ((z : Nat) (s : (Π (x : Nat) Nat)))))]
]
Next, we define addition.
@nested[#:style 'code-inset
@render-term[
(λ (n : Nat)
  (λ (m : Nat)
    (elim Nat (λ (x : Nat) Nat) ()
      (m
       (λ (n-1 : Nat)
         (λ (ih : Nat)
           (s ih))))
     n)))]
]
Note that in Cur @render-term[n-1] is a valid identifier.

We annotate the eliminator with the type @render-term[D] being eliminated.

The next argument to the eliminator is the @emph{motive}, a type constructor
used to compute the result type of the elimination.
The motive is a function that takes the indices of the inductive type and the
argument being eliminated, and computes the return type.
In this case, the motive is @render-term[(λ (x : Nat) Nat)], a constant
function that tells us the result type of addition is @render-term[Nat].

The next argument is a sequence of indices for the inductive type.
The indices are given to the motive during type checking to compute the result
type.
There are no indices in this example, since @render-term[Nat] is not an indexed
type.

The next argument is a sequence of are @emph{methods}.
The eliminator requires one method for each constructor of the inductive type
being eliminated.
For natural numbers, there are two constructors and thus two methods.
Each method takes the arguments to its corresponding constructor and
@emph{inductive hypotheses}, the result of recursively eliminating the
recursive arguments to the constructor.
The method for @render-term[z] is just the constant @render-term[m]; it takes
no arguments since the constructor @render-term[z] takes no arguments.
The method for @render-term[s] takes two arguments: one for the argument to
@render-term[s] and one for the recursive elimination of that argument, since
the argument is also a @render-term[Nat].

The final argument is the @emph{discriminant}, @emph{i.e.}, the value to
eliminate, in this case the argument @render-term[n].

The bottom of @Figure-ref{fig:curnel-syntax} presents the small-step reduction
of Curnel.
The dynamic semantics of Curnel are standard, with β-reduction and folds over
inductive types @render-term[D].
The fold over an inductive type takes a step when the discriminant is a fully applied
constructor @render-term[c] of the inductive type @render-term[D].
we step to the method corresponding to the constructor applied to arguments
@render-term[Θ_mi], where these arguments are computed from the indices, the
constructor's arguments, and the recursive application of the eliminator to
recursive arguments.
We omit the definitions of various meta-functions used in the reduction
relation as they are not instructive.
We extend these small-step rules for a call-by-value normalization strategy in
the usual way.

Rather than explain in more detail the semantics of eliminators in general, we
give an example reducing an eliminator.
Continuing with our addition example, suppose we have called the addition
function with @render-term[(s z)] and @render-term[z].
Then the eliminator will take a step as follows:
@nested[#:style 'code-inset
@render-term[
(elim Nat o_ () (m_0 m_1) (s z))]
" → "
@render-term[
((m_1 z) (elim Nat o_ () (m_0 m_1) z))]
@verbatim|{

|@elem{where:}
 |@render-term[U] = |@render-term[(Unv 0)]
 |@render-term[o_] = |@render-term[(λ (x : Nat) Nat)]
 |@render-term[m_0] = |@render-term[z]
 |@render-term[m_1] = |@render-term[(λ (n-1 : Nat) (λ (ih : Nat) (s ih)))]
}|
]
Since the eliminator is applied to @render-term[(s z)], the second constructor
for @render-term[Nat], we step to a use of the second method @render-term[m_1].
We pass this method the argument to @render-term[s], and recursively eliminate
that argument.
@figure**["fig:curnel-types" "Cur's Type System (excerpts)"
@render-mathpar-judgment[(unv-type 1) (unv-pred 3)]
@(linebreak)
@(hline 600 .75 #:segment 5)
@(linebreak)
@render-mathpar-judgment[(subtype 3)]
@(linebreak)
@(hline 600 .75 #:segment 5)
@(linebreak)
@render-mathpar-judgment[(type-check 1) (type-infer 8)]
]

The type system of Curnel is a standard intuitionistic dependent-type theory,
but we will present it briefly so that readers are aware of any differences
between our system and existing proof assistants.
@Figure-ref{fig:curnel-types} presents the type system.

Starting at the top of the figure, the judgment
@render-term[(unv-type U_0 U_1)] gives typing for universes.
Each universe @render-term[(Unv i)] has the type @render-term[(Unv (add1 i))].

The judgment @render-term[(unv-pred U_0 U_1 U_2)] encodes the predicativity
rules for universes and the types of function spaces.
We use predicativity rules similar to Coq; functions are impredicative
in @render-term[(Unv 0)], but are predicative in all higher universes.
Unlike Coq, we do not distinguish between Prop and Set.

The subtyping judgment @render-term[(subtype Δ Γ t_0 t_1)], in the middle
of @Figure-ref{fig:curnel-types}, defines when the type @render-term[t_0] is
a subtype of the type @render-term[t_1].
A type @render-term[t_0] is a subtype of @render-term[t_1] if
they @emph{equivalent}, @emph{i.e.}, they reduce to α-equivalent terms in the
dynamic semantics.
Any universe is a subtype of any higher universe.
A function type @render-term[(Π (x : t_0) e_0)] is a subtype of another
function type @render-term[(Π (x : t_1) e_1)] if @render-term[t_0] is
@emph{equivalent} to @render-term[t_1], and @render-term[e_0] is a subtype of
@render-term[e_1].
Note that we cannot allow @render-term[t_0] to be a subtype of
@render-term[t_1] due to predicativity rules.

In the bottom of the figure, we define term typing.
We separate term typing into two judgments to simplify algorithmic
implementation of convertibility during type checking.
The type-inference judgment @render-term[(type-infer Δ Γ e t)]
infers the type @render-term[t] for the term @render-term[e]
under term environment @render-term[Γ] and declarations
@render-term[Δ].
Note that this inference is trivial since Curnel terms are fully annotated.
Without loss of generality, we assume the inference judgment can return a type
in normal form if required.

The type-checking judgment @render-term[(type-check Δ Γ e t)]
checks that term @render-term[e] has a type @render-term[t_0] that is
convertible to the type @render-term[t].
As the type of the eliminator is standard we omit the presentation.
