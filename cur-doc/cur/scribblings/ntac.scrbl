#lang scribble/manual

@(require
  "defs.rkt"
  racket/contract
  scribble/eval
  (for-label
   (only-in racket
            identifier? syntax? boolean? syntax dict? listof exn:fail string? let any
            [-> r:->])
   racket/syntax
   (only-meta-in 0 cur)
   (only-meta-in 0 cur/stdlib/nat)
   (only-meta-in 0 cur/stdlib/bool)
   (only-in (only-meta-in 0 cur/curnel/coc-saccharata) ∀ forall ->)
   (only-meta-in 0 cur/stdlib/equality)
   (only-in cur/ntac/base ntac ntac-proc)
   (except-in cur/ntac/hint ntac ntac-proc) @;{ TODO: fixme }
   cur/ntac/standard
   cur/ntac/rewrite))


@title{ntac: The New Tactic System}

@author[@author+email["William J. Bowman" "wjb@williamjbowman.com"]]
@author[@author+email["Jay McCarthy" "jay@racket-lang.org"]]
@author[@author+email["Stephen Chang" "stchang@ccs.neu.edu"]]

As Coq has shown, tactics have proven useful for doing complex proofs.
In Cur, tactics are not built-in or provided by the language.
However, any user can use meta-programming to add tactics to Cur.
In fact, a user did.
Cur originally shipped with a proof-of-concept tactic system, but the system did not scale well.
So Jay designed and prototyped a new one over a weekend in 200 lines of code.
Now it's the default system.

@section{The ntac system}
@defmodule[cur/ntac/base]

A @tech{tactic} is used at the top-level of a proof script.
A @deftech{tactic} is a Racket function that satisfies the contact @racket[(r:->
nttz? nttz?)] (where @racket[r:->] is the Racket function contract normally
written @code{->}; we use @racket[r:->] since Cur redefined @racket[->]).
Tactics easily compose, may navigate the proof tree, resolve multiple holes, and
be called recursively.

A @tech{tactical} is used to manipulate the focus of proof tree, such as to
resolve a single hole.
A @deftech{tactical} satisfies the contract @racket[(r:-> dict? ntt?)]
We will conflate tacticals with functions that produce tacticals from addition
arguments.
I.e. we also call functions that satisfy @racket[(r:-> syntax? ... (r:-> dict? ntt?))] tacticals.
Tacticals receive additional arguments as Cur syntax; for technical reasons
these need to be processed by @racket[ntac-syntax] before being used in a
tactical.
Tacticals are usually used by the @racket[fill] tactic, which simply applies a
tactical to the current focus of the proof tree zipper.
We usually provide macros for the surface syntax of tacticals so that users
need not deal with syntax objects directly, or explicitly use the @racket[fill]
tactic.
These macros follow the naming convention @racket[by-_tactical].

@(define curnel-eval
   (curnel-sandbox
    "(require cur/ntac/hint cur/ntac/standard cur/ntac/rewrite cur/stdlib/sugar cur/stdlib/nat cur/stdlib/bool cur/stdlib/equality)")) @;{ TODO: fixme }

@subsection{Usage}

@defform[(ntac type tactic ...)]{
Run the ntac @racket[tactic ...] to produce a term inhabiting @racket[type].

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-intro by-assumption)
 z)

(eval:alts
 ((ntac (forall (x : Nat) Nat)
  interactive)
 z)
 ((ntac (forall (x : Nat) Nat)
  by-obvious)
 z))
]
}

@defform[(define-theorem name ty ps ...)]{
Short hand for @racket[(define name (ntac ty ps ...))]
@examples[#:eval curnel-eval
(define-theorem nat-id (forall (x : Nat) Nat)
  by-intro by-assumption)
]
}

@subsection{Base Tactics}
These tactics are used in the tactic system API, while other other tactics are defined outside the base system.

@defthing[next tactic?]{
Move the focus to the next hole.
}

@subsection{Proof Trees}

@todo{The internal details of the tactic system should be de-emphasized, and
the tactics that programmers actually want to use should be more
prominent. These next few subsections should probably be moved to the end of
the documentation.}

The @emph{nt}ac proof @emph{t}ree datatype @racket[ntt] represents a Cur term with holes.
Specifically, the proof tree contains nodes for a hole, an exact term,
a combination of subterms, and a context manipulation.

@defstruct*[ntt ([contains-hole? boolean?] [goal syntax?]) #:transparent]{
An ntac proof tree. Records the current @racket[goal], as syntax representing a Cur type, and whether or not there is a hole.
}

@defstruct*[(ntt-hole ntt) ([contains-hole? boolean?] [goal syntax?]) #:transparent]{
A node in an ntac proof tree representing a hole to be filled.
}

@defproc[(make-ntt-hole [goal syntax?]) ntt?]{
Create a new @racket[ntt-hole?] node whose hole is @racket[goal?].
The resulting @racket[ntt?] does @racket[contains-hole?].
}

@defstruct*[(ntt-exact ntt) ([contains-hole? boolean?] [goal syntax?] [term syntax?]) #:transparent]{
A node in an ntac proof tree holding a Cur @racket[term], as @racket[syntax?], satisfying @racket[goal].
}

@defproc[(make-ntt-exact [goal syntax?] [term syntax?]) ntt?]{
Create a new @racket[ntt-exact?] node that proves @racket[goal] via the Cur
term @racket[term].
The resulting @racket[ntt?] does not @racket[contains-hole?].
}

@defstruct*[(ntt-context ntt) ([contains-hole? boolean?] [goal syntax?] [env-transformer (r:-> dict? dict?)] [subtree ntt?]) #:transparent]{
A node in an ntac proof tree that records information about the local environment, by manipulating the context of the @racket[subtree] using @racket[env-transformer].
}

@defproc[(make-ntt-context [env-transformer (r:-> dict? dict?)] [subtree ntt?]) ntt?]{
Create a new @racket[ntt-context?] node that manipulates the @racket[subtree]
according to @racket[env-transformer].
The resulting @racket[ntt?] inherits the @racket[goal] from @racket[subtree] and
only @racket[contains-hole?] if @racket[subtree] does.
}

@defstruct*[(ntt-apply ntt) ([contains-hole? boolean?] [goal syntax?] [subtrees (listof ntt?)] [f (r:-> syntax? ... syntax?)]) #:transparent]{
A node in an ntac proof tree that proves @racket[goal] by using @racket[f] to combine the terms that result from @racket[subtrees] into a single Cur term.
}

@defproc[(make-ntt-apply [goal syntax?] [subtrees (listof ntt)] [f (r:-> syntax? ... syntax?)]) ntt?]{
Create a new @racket[ntt-apply?] node that uses @racket[f] to build a proof tree out of @racket[subtrees], with @racket[goal] remaining to be proved.
The resulting @racket[ntt?] @racket[contains-hole?] if any @racket[subtrees] do.
}

@defstruct*[(ntt-done ntt) ([contains-hole? boolean?] [goal syntax?] [subtree ntt?]) #:transparent]{
A node in an ntac proof tree that asserts that the @racket[subtree] is complete.
}

@defproc[(make-ntt-done [subtree ntt?]) ntt?]{
Create a new @racket[ntt-done?] node with @racket[subtree].
Results in an error if @racket[subtree] @racket[contains-hole?].
}

@subsection{Proof Tree Zipper}
To navigate the proof tree, we define the @emph{nt}ac @emph{t}ree @emph{z}ipper.

@todo{Actually, these dicts need to be ordered-dicts or envs. Also, right now they're hashes}
@todo{Should we hide the details of this struct?}
@defstruct*[nttz ([context dict?] [focus ntt?] [prev (r:-> ntt? nttz?)])]{
An ntac tree zipper.
Contains the local environment for the focus of the proof tree,
@racket[context], the subtree being focused on @racket[focus], and a function
that navigates up the tree once the focused subtree is complete @racket[prev].
}

@defproc[(nttz-up [nttz nttz?]) nttz?]{
Navigate up the proof tree.
}

@defproc[(nttz-down-context [nttz nttz?]) nttz?]{
Navigate down when the proof tree when the focus is a context node.
}

@defproc[(nttz-down-apply [nttz nttz?]) nttz?]{
Navigate down when the proof tree when the focus is an apply node.
}

@defproc[(nttz-done? [nttz nttz?]) boolean?]{
Returns @racket[#t] when the focus is complete, and @racket[#f] otherwise.
}

@subsection{Tactic System API}
@defproc[(new-proof-tree [goal syntax?]) ntt?]{
Create a new proof tree with @racket[goal].
}

@defproc[(proof-tree->complete-term [pt ntt?] [err-stx syntax? #f]) syntax?]{
Run a the proof tree @racket[pt] to produce a Cur term, as syntax. Raise an
error if the proof tree @racket[contains-hole?], using @racket[err-stx] for
error location.
}

@defproc[(eval-proof-step [ptz nttz?] [pstep syntax?]) nttz?]{
Evaluate the tactic represented by @racket[pstep] on @racket[ptz],
performing error handling.
}

@defproc[(eval-proof-script [pt ntt?] [psteps (listof syntax?)] [err-stx syntax? #f]) ntt?]{
Evaluate the tactic script represented by @racket[psteps] on the proof tree
@racket[pt], checking that the resulting proof is valid for the goal of
@racket[pt] and producing an error otherwise, using @racket[err-stx] for error location.
}

@defproc[(ntac-proc [goal syntax?] [ps (listof syntax?)]) syntax?]{
A procedure version of @racket[ntac].
Runs the proof script represented by @racket[ps] to produce a Cur term of type
represented by @racket[goal].
}

@defproc[(ntac-syntax [stx syntax?]) syntax?]{
For technical reasons, top-level syntax objects representing Cur terms need to
be processed before being used in a tactical.
This function performs that processing.
Usually, this function is used in a macro that provides surface syntax for a tactical.
}

@subsection{theorem-info}

@defstruct*[(theorem-info identifier-info) ([name identifier?] [orig
syntax?])]{ Representation for theorems defined with
@racket[define-theorem]. Needed because the actual binding may have normalized
the original theorem. }

@; section: Standard Tactics and Tacticals ----------------------------------------

@section{Standard Tactics and Tacticals}
@defmodule[cur/ntac/standard]

@defstruct*[(exn:fail:ntac exn:fail) ()]{
A phase 1 value; an exception representing an ntac failure.
}

@defstruct*[(exn:fail:ntac:goal exn:fail:ntac) ()]{
A phase 1 value; an exception representing an failure for an ntac tactic or tactical to match against the current goal.
}

@defproc[(raise-ntac-goal-exception [msgf string?] [arg string?] ...) any]{
A phase 1 procedure; raises @racket[exn:fail:ntac:goal], using the format string @racket[msgf] with arguments @racket[arg]s to format the error message.
}

@defform[(ntac-match goal [pattern branch] ...)]{
A phase 0 form; like @racket[cur-match], but implicitly raises @racket[exn:fail:ntac:goal] if none of the @racket[pattern]s match.
}

@todo{Create deftactic and deftactical?}
@defthing[nop tactic?]{
The no-op tactic; does nothing.
}

@defproc[(exact [e syntax?]) tactical?]{
Fills the current hole with exactly @racket[e], using @racket[ntt-exact].}

@defthing[display-focus tactic?]{
Print the focus of the proof tree, and its local environment.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  display-focus by-intro display-focus by-assumption)
 z)
]
}

@defproc[(try [t tactic?]) tactic?]{
Runs the tactic @racket[t] on the proof tree, but ignore any @racket[exn:fail:ntac:goal]s and return the proof tree unchanged if such an exception is raised.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-assumption)
 z)
((ntac (forall (x : Nat) Nat)
  (try by-assumption))
 z)
]
}

@defproc[(fill [t tactical?]) tactic?]{
Runs the tactical @racket[t] on the focus of the proof tree.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  (fill (intro)) by-assumption)
 z)
]
}

@defproc[(intro [name identifier? #f]) tactical?]{
Matches when the current goal has the form @racket[(forall (id : type-expr)
body-expr)], introducing the assumption @racket[name : type-expr] into the
local environment, using @racket[id] if no @racket[name] is provided.
Raises @racket[exn:fail:ntac:goal] if the goal does not have the this form.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  (fill (intro)) by-assumption)
 z)

((ntac (forall (x : Nat) Nat)
  (fill (intro (ntac-syntax #'x))) by-assumption)
 z)
]
}

@defform*[((by-intro id)
           by-intro)]{
Short hand for @racket[(fill (intro #'id))] and @racket[(fill (intro))], respectively.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-intro by-assumption)
 z)
]
}

@defform[(by-intros id ...)]{
Shorthand for @racket[(by-intro id) ...].
}

@defthing[assumption tactical?]{
Solves the goal by looking for a matching assumption in the local environment.
Raises @racket[exn:fail:ntac:goal] if not assumption matches the goal.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-intro (fill assumption))
 z)
]
}

@todo{Maybe just define the macro @racket[by] that expands to @racket[(fill (tactical rest ...))]}
@defform[#:id by-assumption by-assumption]{
Short hand for @racket[(fill (assumption))]

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-intro by-assumption)
 z)
]
}

@defthing[obvious tactical?]{
Attempts to solve a goal by doing the obvious thing.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  (fill obvious) (fill obvious))
 z)
]
}

@todo{This breaks the naming convention; probably should have obvious-step and obvious}
@defthing[by-obvious tactic?]{
Try to solve all the holes by doing the obvious thing.

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-obvious)
 z)
]
}


@; assert ----------------------------------------

@defform[(by-assert name thm)]{

Short hand for @racket[(fill (assert #'name #'thm))].

@examples[#:eval curnel-eval
((ntac
  (∀ [x : Nat] [y : Nat]
     (-> (== Nat x y)
         (== Nat y x)))
  (by-intros x y x=y)
  @code:comment{define local thm named y=x}
  (by-assert y=x (== Nat y x))
  @code:comment{prove y=x}
  display-focus
  (by-rewriteR x=y)
  display-focus
  reflexivity
  @code:comment{prove original goal using y=x}
  display-focus
  (by-assumption y=x))
 1 1 (refl Nat 1))
]
}

@defproc[(assert [name identifier?] [thm syntax?]) tactical?]{

Shifts the goal to defining @racket[thm]. When @racket[thm] is proven, shifts
the goal to the original goal, but with @racket[name] bound to @racket[thm] in
the context.
}

@; simpl ----------------------------------------


@defthing[simpl tactic?]{

Simplifies the current goal by evaluating it.

@examples[#:eval curnel-eval
(define-theorem plus_1_l
  (∀ [n : Nat] (== Nat (plus 1 n) (s n)))
  by-intro
  display-focus
  simpl
  display-focus
  reflexivity)
]
}



@; destruct ----------------------------------------

@defform*[((by-destruct name)
           (by-destruct name #:as param-namess))]{

Short hand for @racket[(fill (destruct #'x))] or @racket[(fill (destruct #'x #'param-namess))].

@examples[#:eval curnel-eval
(define-theorem plus-1-neq-0
  (∀ [n : Nat] (== Bool (nat-equal? (plus 1 n) 0) false))
  (by-intro n)
  display-focus
  (by-destruct n #:as [() (n-1)])
  @code:comment{zero case}
  display-focus
  simpl
  display-focus
  reflexivity
  @code:comment{succ case}
  display-focus
  simpl
  display-focus
  reflexivity)
(plus-1-neq-0 0)
(plus-1-neq-0 1)
]
}

@defproc[(destruct [name identifier?] [param-namess syntax? #f]) tactical?]{

Splits the goal into @racket[n] subgoals, where
@racket[n] is the number of possible cases for @racket[name].

The resulting proof term uses @racket[match].

@racket[param-namess] should be a list of list of identifiers, which are used
as the binders in each clause. If not specified, the original binder names from
the @racket[data] declaration are used. Does not include induction hypotheses
for recursive arguments.

}

@; induction ----------------------------------------

@defform[(by-induction name #:as param-namess)]{

Short hand for @racket[(fill (induction #'x #'param-namess))].

@examples[#:eval curnel-eval
(define-theorem plus-n-0
  (∀ [n : Nat] (== Nat n (plus n z)))
  (by-intro n)
  simpl ;; this step doesnt do anything except get everything in expanded form
  (by-induction n #:as [() (n-1 IH)])
  @code:comment{zero case}
  display-focus
  reflexivity
  @code:comment{succ case}
  display-focus
  simpl
  display-focus
  (by-rewriteL IH)
  display-focus
  reflexivity)
]
}

@defproc[(induction [name identifier?] [param-namess syntax?]) tactical?]{

Splits the goal into @racket[n] subgoals, where
@racket[n] is the number of possible cases for @racket[name].

Unlike @racket[destruct], @racket[induction] binds an induction hypothesis for
recursive arguments in each case.

The resulting proof term uses @racket[new-elim].

@racket[param-namess] should be a list of list of identifiers, which are used
as the binders in each clause. If not specified, the original binder names from
the @racket[data] declaration are used.

}


@; interactive ----------------------------------------

@subsection{Interactive Tactic}
In Cur, interactivity is just a user-defined tactic.

@defthing[interactive tactic?]{
Starts a REPL that prints the proof state, reads a tactic (as @racket[ntac] would), evaluates the
tactic, and repeats. Exits when the proof is finished.
Handles @racket[exn:fail:ntac:goal] by printing the message and continuing the REPL.

@examples[#:eval curnel-eval
(eval:alts
((ntac (forall (x : Nat) Nat)
  interactive)
 z)
 ((ntac (forall (x : Nat) Nat)
  by-obvious)
 z))
]
}

@; auto ----------------------------------------

@section{Auto-related Tactics}
@defmodule[cur/ntac/hint]
Ntac provides an automatic proof solving tactic that generates proof steps
using pairs of tactic presets and identifiers from the current context and a
user-defined hints database.

@defthing[auto tactic?]{
The Cur implementation of @hyperlink["https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto" "Coq's auto"].

We first try @racket[by-obvious] for trivial goals. If this fails, we then
introduce each variable to context and exhaustively attempt pairings of preset
tactics and identifiers.

The tactic returns when either the @racket[goal] has
been completed or the maximum number of tactic applications specified by
@racket[current-max-auto-depth] has been reached.

@examples[#:eval curnel-eval
  (define-theorem plus-n-0
    (∀ [n : Nat] (== Nat n (plus n 0)))
      auto)
]
}

@defthing[current-max-auto-depth parameter?]{
A phase 1 parameter for defining the maximum search depth for @racket[auto]. By
default, up to 4 tactics are applied to the initial tree zipper state before
failure.
}

@defthing[current-hints parameter?]{
A phase 1 parameter denoting the current hints database used by @racket[auto]. By
default, this parameter is empty.

Uses a @racket[guard] to ensure that values are ordered and unique. The ordering
of the hints determines the order of @racket[tactic] application.
}

@defthing[display-hints tactic?]{
Print the local hints database.
}

@defform[(define-theorem #:hints (hint ...) name ty ps ...)]{
Short hand for @racket[(define name (ntac ty ps ...))].

Optionally allows for specification of a hints database scoped to the theorem.
               
@examples[#:eval curnel-eval
(define-theorem pred-example-1
  (∀ [p : Bool]
     (== (and p p) p))
  (by-intros p)
  (by-destruct p)
  reflexivity
  reflexivity)
(define-theorem pred-example-2
  #:hints (pred-example-1)
  (∀ [p : Bool] [q : Bool]
     (-> (== p q)
         (== p true)
         (== (and p q) true)))
  display-hints
  auto)
]
}

@defform[(hints hint ...)]{
Create a new hints database closure extending @racket[current-hints] while
prepending the specified list of hints.

@examples[#:eval curnel-eval
(define-theorem pred-example-1
  (∀ [p : Bool]
     (== (and p p) p))
  (by-intros p)
  (by-destruct p)
  reflexivity
  reflexivity)
(define-theorem pred-example-2
  #:hints (pred-example-1)
  (∀ [p : Bool] [q : Bool]
     (-> (== p q)
         (== p true)
         (== (and p q) true)))
  display-hints
  (hints (pred-example-2) display-hints)
  display-hints
  auto)
]
}

@defstruct*[tactic-preset ([proc tactic?] [id syntax?] [no-name-arg? boolean?]) #:transparent]{
A preset definition of a @racket[tactic]. Includes metadata for the desired
identifier and whether the tactic consumes an identifier when invoked.
}

@defthing[current-auto-tactics parameter?]{
A phase 1 parameter for denoting the list of @racket[tactic-preset] to try for @racket[auto].

The ordering of the presets determines execution order, so it is recommended to
arrange base cases first (e.g. @racket[by-assumption]).
}

@; rewrite subsec ----------------------------------------

@section{Rewrite-related Tactics}
@defmodule[cur/ntac/rewrite]

Ntac includes @emph{two} libraries of rewrite tactics: one (the above)
for "standard" Paulin-Mohring equality (ie, @racket[==]), and
another (@tt{cur/ntac/ML-rewrite}) for Martin-Lof equality (i.e.,
@racket[ML-=]).

Each library provides versions of the following bindings.


@; reflexivity ----------------------------------------


@defthing[reflexivity tactic?]{

For a goal @racket[(== A a b)], shorthand for @racket[(fill (exact #'(refl A a)))].
}

@; Rewrite tactics ----------------------------------------
@defform[(by-rewrite name . es)]{

Rewrites the current goal with @racket[name], instantiating with @racket[es] if necessary.

Rewrites from right-to-left (equivalent to Coq's @tt{->}), i.e.,
for a theorem @racket[(== A x y)], @racket[x] is replaced with @racket[y].

Short hand for @racket[(fill (rewrite #'name #:es #'es))].

Equivalent to @racket[by-rewriteR].

@examples[#:eval curnel-eval
(define-theorem identity-fn-applied-twice
  (∀ [f : (-> Bool Bool)]
     (-> (∀ [x : Bool] (== Bool (f x) x))
         (∀ [b : Bool] (== Bool (f (f b)) b))))
  (by-intros f H b)
  display-focus
  (by-rewrite H b)
  display-focus
  (by-rewrite H b)
  display-focus
  reflexivity
)
]
}

@defform[(by-rewriteR name . es)]{

Rewrites the current goal with @racket[name], instantiating with @racket[es] if necessary.

Rewrites from right-to-left (equivalent to Coq's @tt{->}), i.e.,
for a theorem @racket[(== A x y)], @racket[x] is replaced with @racket[y].

Short hand for @racket[(fill (rewrite #'name #:es #'es))].

Equivalent to @racket[by-rewrite].
}

@defform[(by-rewriteL name . es)]{

Rewrites the current goal with @racket[name], instantiating with @racket[es] if necessary.

Short hand for @racket[(fill (rewrite #'name #:es #'es #:left? #t))].

Rewrites from left-to-right (equivalent to Coq's @tt{<-}), i.e.,
for a theorem @racket[(== A x y)], @racket[y] is replaced with @racket[x].
}

@; rewrite ----------------------------------------
@defproc[(rewrite [name identifier?] [#:left? left? boolean? #f]
                                     [#:es es syntax? #'()]
                                     [#:thm-name thm-name identifier? #f]
                                     [#:thm thm syntax? #f])
          tactical?]{

Rewrites the current goal with @racket[name], instantiating with @racket[es] if necessary.

By default, rewrites from right-to-left (equivalent to Coq's @tt{->}), i.e.,
for a theorem @racket[(== A x y)], @racket[x] is replaced with @racket[y]. If
@racket[left?] is @racket[#t], rewrites from left-to-right instead (Coq's
@tt{<-}).

}

@; replace ----------------------------------------
@defform[(by-replace ty from to)]{
Shorthand for @racket[(fill (replace #'ty #'from #'to))].

Replaces instances of @racket[from] in the goal, which has type @racket[ty],
with @racket[to]. Adds @racket[ty] as a subgoal.

@examples[#:eval curnel-eval
(define-theorem plus-n-Sm
    (∀ [n : Nat] [m : Nat]
       (== Nat (s (plus n m)) (plus n (s m))))
    (by-intro n)
    (by-intro m)
    simpl
    (by-induction n #:as [() (n-1 IH)])
    ; zero case
    simpl
    reflexivity
    ; succ case
    simpl
    (by-rewrite IH)
    reflexivity)
(define-theorem plus_comm
    (∀ [n : Nat] [m : Nat]
       (== Nat (plus n m) (plus m n)))
    (by-intro n)
    (by-intro m)
    simpl
    (by-induction n #:as [() (n-1 IH)])
    ; zero case
    simpl
    display-focus
    (by-rewriteL plus-n-0 m)
    display-focus
    reflexivity
    ; succ case
    simpl
    (by-rewriteL plus-n-Sm m n-1)
    (by-rewrite IH)
    reflexivity)
(define-theorem plus-assoc
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p)) (plus (plus n m) p)))
  (by-intros n m p)
  simpl
  (by-induction n #:as [() (n-1 IH)])
  @code:comment{zero case}
  reflexivity
  @code:comment{succ case}
  simpl
  (by-rewrite IH)
  reflexivity)
(define-theorem plus-swap
  (∀ [n : Nat] [m : Nat] [p : Nat]
     (== Nat (plus n (plus m p))
               (plus m (plus n p))))
  (by-intros n m p)
  (by-rewrite plus-assoc n m p)
  display-focus
  (by-replace Nat (plus n m) (plus m n))
  display-focus
  (by-rewriteL plus-assoc m n p)
  reflexivity
  @code:comment{proof of by-replace theorem}
  display-focus
  (by-rewrite plus_comm m n)
  display-focus
  reflexivity)
]
}

@defproc[(replace [ty syntax?] [from syntax?] [to syntax?]) tactical?]{

Replaces instances of @racket[from] in the goal, which has type @racket[ty],
with @racket[to].
}


