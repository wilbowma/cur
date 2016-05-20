#lang scribble/base
@(require
  "defs.rkt"
  "cur.rkt"
  "bib.rkt"
  scribble/manual
  scriblib/figure
  racket/function)

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
"felleisen2009semantics"] and most figures in this section are extracted from
the Redex implementation, so some notation may be slightly non-standard.
@figure["fig:curnel-syntax" "Curnel Syntax and Dynamic Semantics"
@(render-language ttL)
@(linebreak)
@(linebreak)
@tabular[#:sep @hspace[1]
(list
  (list (render-term ((λ (x : t) e_0) e_1)) "→" (render-term (subst e_0 x e_1)))
  (list (render-term ((elim D U) o_ m_0 ... m_i m_i+1 ... m_n i_ ... (c_i a_ ... y_ ...)))
        "→"
        (render-term (m_i a_ ... ih_ ...))))
]]

The top of @Figure-ref{fig:curnel-syntax} presents the syntax of Curnel.
A Curnel term is either a universe @render-term[U], a function
@render-term[(λ (x : t) e)], a variable, a dependent function type
@render-term[(Π (x : t) t)], an application @render-term[(e e)], or the
elimination of an inductive type @render-term[(elim D U)].
We write universes of level @render-term[i] as @render-term[(Unv i)].
We usually write variables using the meta-variable @render-term[x],
but we use @render-term[D] for the name of declared inductive types and
@render-term[c] for the names of inductive-type constructors.
We annotate the inductive-type eliminator @render-term[(elim D U)] with the
inductive type @render-term[D], and the universe of the return type
@render-term[U] to simplify type inference.

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
First we define the natural number:
@nested[#:style 'code-inset
  @render-term[(∅ (Nat : (Unv 0) ((z : Nat) (s : (Π (x : Nat) Nat)))))]
]
Next, we define addition.
We intentionally use the precise syntax of the language in this example and
take no liberties with syntactic sugar.
The definition of addition has many leading and trailing parenthesis because
Curnel has only single-arity functions.
We will come back to this in @secref{sec:surface} when we implement multi-arity
functions via language extension.
@nested[#:style 'code-inset
@render-term[
(λ (n : Nat)
  (λ (m : Nat)
    (((((elim Nat (Unv 0))
        (λ (x : Nat) Nat))
       m)
      (λ (n-1 : Nat)
        (λ (ih : Nat)
          (s ih))))
     n)))]
]
We annotate the eliminator with @render-term[(Unv 0)] since the result of plus
is a @render-term[Nat], which is in universe @render-term[(Unv 0)].

The next argument to the eliminator is the @emph{motive}, a type constructor
used to compute the result type of the elimination.
The motive is a function that takes the indices of the inductive type and the
argument being eliminated, and computes the return type.
In this case, the motive is @render-term[(λ (x : Nat) Nat)], a constant
function that tells us the result type of addition is @render-term[Nat].

The next two arguments are @emph{methods}.
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

After the methods, the eliminator expects the indices for the inductive type.
The indices are given to the motive during type checking to compute the result
type.
There are no indices in this example, since @render-term[Nat] is not an indexed
type.

The final argument is the value to eliminate, in this case the argument
@render-term[n].

The bottom of @Figure-ref{fig:curnel-syntax} presents a sketch of the dynamic
semantics.
The Redex implementation of reduction for @render-term[(elim D U)] is somewhat
involved, so we informally sketch the small-step reduction rules rather than
extract a figure from Redex.
The dynamic semantics of Curnel are standard, with β-reduction and folds over
inductive types @render-term[D] defined by @render-term[(elim D U)].

Rather than explain the semantics of eliminators general, we give an example
reducing an eliminator.
This time, we do take liberties with syntax for clarity.
Continuing with our addition example, suppose we have called the addition
function with @render-term[(s z)] and @render-term[z].
Then the eliminator will take a step as follows:
@nested[#:style 'code-inset
@render-term[
((elim Nat U) o_ m_0 m_1 (s z))]
" → "
@render-term[
(m_1 z ((elim Nat U) o_ m_0 m_1 z))]
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
@(vc-append 10
   (hb-append 20
     (render-judgment-form unv-type)
     (parameterize ([relation-clauses-combine (λ (l) (apply hb-append 20 l))])
       (render-judgment-form unv-pred)))
   (hline 600 .75 #:segment 5)
   (parameterize ([relation-clauses-combine (λ (l) (apply hb-append 20 l))])
     (render-judgment-form convert))
   (hline 600 .75 #:segment 5)
   (hb-append 20 (render-judgment-form type-check)
     (parameterize ([judgment-form-cases (build-list 2 values)]
                    [relation-clauses-combine (λ (l) (apply hb-append 20 l))])
       (render-judgment-form type-infer)))
   (parameterize ([judgment-form-cases (build-list 3 (curry + 2))]
                  [relation-clauses-combine (λ (l) (apply hb-append 20 l))])
     (render-judgment-form type-infer))
   (parameterize ([judgment-form-cases (build-list 2 (curry + 5))]
                  [relation-clauses-combine (λ (l) (apply hb-append 20 l))])
     (render-judgment-form type-infer)))
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

The convertibility judgment @render-term[(convert Δ Γ t_0 t_1)], in the middle
of @Figure-ref{fig:curnel-types}, defines when the type @render-term[t_0] is
convertible to the type @render-term[t_1].
Any universe is convertible to any higher universe.
A function type @render-term[(Π (x : t_0) t_1)] is convertible to another
function type @render-term[(Π (x : t_0) t_2)] if @render-term[t_1] is
convertible to @render-term[t_2].
Finally, a type @render-term[t_0] is convertible to @render-term[t_1] if
they reduce to α-equivalent terms in the dynamic semantics.
The meta-function @render-term[(reduce Δ e)] used in the convertibility
judgment normalizes the term @render-term[e] with the inductive types declared
by @render-term[Δ] using a call-by-value semantics.

In the bottom of the figure, we define term typing.
We separate term typing into two judgments to simplify algorithmic
implementation of convertibility during type checking.
The type-inference judgment @render-term[(type-infer Δ Γ e t)]
infers the type @render-term[t] for the term @render-term[e]
under term environment @render-term[Γ] and declarations
@render-term[Δ].
Note that this inference is trivial since Curnel terms are fully annotated.

The type-checking judgment @render-term[(type-check Δ Γ e t)]
checks that term @render-term[e] has a type @render-term[t_0] that is
convertible to the type @render-term[t].
The type of the inductive eliminator @render-term[(elim D U)] is computed by
the meta-function @render-term[Δ-elim-type].
As the type of the eliminator is standard we omit the presentation.
