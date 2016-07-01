#lang scribble/manual

@(require
  "defs.rkt"
  racket/contract
  (for-label racket)
  scribble/eval)

@title{ntac: The New Tactic System}

@author[@author+email["William J. Bowman" "wjb@williamjbowman.com"]]
@author[@author+email["Jay McCarthy" "jay@racket-lang.org"]]

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
A @deftech{tactic} is a Racket function that satisfies the contact @racket[(-> nttz? nttz?)]
Tactics easily compose, may navigate the proof tree, resolve multiple holes, and
be called recursively.

A @tech{tactical} is used to manipulate the focus of proof tree, such as to
resolve a single hole.
A @deftech{tactical} satisfies the contract @racket[(-> dict? ntt?)]
We will conflate tacticals with functions that produce tacticals from addition
arguments.
I.e. we also call functions that satisfy @racket[(-> syntax? ... (-> dict? ntt?))] tacticals.
Tacticals receive additional arguments as Cur syntax; for technical reasons
these need to be processed by @racket[ntac-syntax] before being used in a
tactical.
Tacticals are usually used by the @racket[fill] tactic, which simply applies a
tactical to the current focus of the proof tree zipper.
We usually provide macros for the surface syntax of tacticals so that users
need not deal with syntax objects directly, or explicitly use the @racket[fill]
tactic.
These macros follow the naming convention @racket[by-_tactical].

@(define curnel-eval (curnel-sandbox "(require cur/ntac/base cur/ntac/standard cur/stdlib/sugar cur/stdlib/nat)"))

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
@todo{define-theorem isn't working on the sandbox}
@examples[#:eval curnel-eval
(eval:alts
(define-theorem nat-id (forall (x : Nat) Nat)
  by-intro by-assumption)
(void))
]
}

@subsection{Base Tactics}
These tactics are used in the tactic system API, while other other tactics are defined outside the base system.

@defthing[next tactic?]{
Move the focus to the next hole.
}

@subsection{Proof Trees}

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

@defstruct*[(ntt-context ntt) ([contains-hole? boolean?] [goal syntax?] [env-transformer (-> dict? dict?)] [subtree ntt?]) #:transparent]{
A node in an ntac proof tree that records information about the local environment, by manipulating the context of the @racket[subtree] using @racket[env-transformer].
}

@defproc[(make-ntt-context [env-transformer (-> dict? dict?)] [subtree ntt?]) ntt?]{
Create a new @racket[ntt-context?] node that manipulates the @racket[subtree]
according to @racket[env-transformer].
The resulting @racket[ntt?] inherits the @racket[goal] from @racket[subtree] and
only @racket[contains-hole?] if @racket[subtree] does.
}

@defstruct*[(ntt-apply ntt) ([contains-hole? boolean?] [goal syntax?] [subtrees (listof? ntt?)] [f (-> syntax? ... syntax?)]) #:transparent]{
A node in an ntac proof tree that proves @racket[goal] by using @racket[f] to combine the terms that result from @racket[subtrees] into a single Cur term.
}

@defproc[(make-ntt-apply [goal syntax?] [subtrees (listof? ntt)] [f (-> syntax? ... syntax?)]) ntt?]{
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
@defstruct*[nttz ([context dict?] [focus ntt?] [prev (-> ntt? nttz?)])]{
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
Short hand for @racket[(fill (intro #'id))] and @racket[(fill (intro))].

@examples[#:eval curnel-eval
((ntac (forall (x : Nat) Nat)
  by-intro by-assumption)
 z)
]
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