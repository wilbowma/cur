#lang scribble/manual

@(require
  "../defs.rkt"
  scribble/eval)

@title{ntac--The New Tactic System}
@defmodule[cur/stdlib/ntac/base]

@author[@author+email["William J. Bowman" "wjb@williamjbowman.com"]]
@author["Jay McCarthy"]

As Coq has shown, tactics have proven useful for doing complex proofs.
In Cur, tactics are not built-in or provided by the language.
However, any user can use meta-programming to add tactics to Cur.
In fact, a user did.
Cur originally shipped with a proof-of-concept tactic system, but the system did not scale well.
So Jay designed and prototyped a new one over a weekend in 200 lines of code.
Now it's the default system.

Ntac tactics are Racket functions defined to manipulate proof trees representing Cur terms with holes.
Ntac supports using tactic scripts inline, in any context that a user might
write a term, or at the top-level for defining and proving theorems.
First we present how to use ntac for those who merely want to do tactic based proving.
Then we discuss the design of the ntac system for those who want to develop tactics and solvers.
@(define curnel-eval (curnel-sandbox "(require cur/stdlib/ntac/base cur/stdlib/ntac/standard cur/stdlib/bool cur/stdlib/nat)"))

@section{Using ntac}
@defmodule[cur/stdlib/ntac/base]

@defform[(ntac-prove type tactics ...)]{
Run the ntac @racket[tactics ...] to produce a term inhabiting @racket[type].
}

@defform[(define-theorem name ty ps ...)]{
Short hand for @racket[(define name (ntac-prove ty ps ...))]
}

@subsection{Standard Tactics and Tacticals}
In ntac, a @deftech{tactic} is a function on proof tree zippers, while a
@deftech{tactical} is a function on proof trees.
Both are Racket functions defined at phase 1.

Tactics are used at the top-level of a proof script.
They may navigate the proof tree, resolves multiple holes, and be called
recursively.

Tacticals are used to manipulate a proof tree in a given context in a simple
way, such as to resolve a single hole.
Tacticals can be called by tactics, but cannot call tactics, solve multiple
holes, or easily manipulate a proof tree recursively.
Tacticals are usually used by the @racket[fill] tactic, which simply applies a
tactical to the current focus of the proof tree zipper
Since tacticals are functions, they receive references to Cur terms as syntax.
We usually provide macros for the surface syntax of tacticals so that users
need not deal with syntax objects directly, or explicitly use the @racket[fill]
tactic.
These macros follow the naming convention @racket[by-_tactical].

@defmodule[cur/stdlib/ntac/standard]

@todo{Create deftactic and deftactical?}
@defthing[#:kind "tactic" nop tactic?]{
The no-op tactic; does nothing.
}

@defproc[#:kind "tactic" (fill [t tactical?]) tactic?]{
Runs the tactical @racket[t] on the focus of the proof tree.
}

@defproc[#:kind "tactical" (intro [name identifier? #f]) tactical?]{
Matches when the current goal has the form @racket[(forall (id : type-expr)
body-expr)], introducing the assumption @racket[name : type-expr] into the
local environment, using @racket[id] if no @racket[name] is provided.
}

@defform*[((by-intro id)
           by-intro)]{
Short hand for @racket[(fill (intro #'id))] and @racket[(fill (intro))].
}

@defthing[#:kind "tactical" assumption tactical?]{
Solves the goal by looking for a matching assumption in the local environment.
}

@defform[#:id by-assumption by-assumption]{
Short hand for @racket[(fill (assumption))]
}

@defthing[#:kind "tactical" obvious tactical?]{
Attempts to solve a goal by doing the obvious thing.
}

@todo{Maybe just define the macro @racket[by] that expands to @racket[(fill (tactical rest ...))]}
@defform[#:id by-obvious by-obvious]{
Short hand for @racket[(fill (obvious))]
}

@subsection{Interactive Tactic}
In Cur, interactivity is just a user-defined tactic.

@defthing[#:kind "tactic" interactive tactic?]{
Starts a REPL that prints the proof state, reads a tactic (as @racket[ntac-prove] would), evaluates the
tactic, and repeats. Exits when the proof is finished.
}

@section{Proof Tree}
@defmodule[cur/stdlib/ntac/base]

ntac tactics manipulate proofs tree. The ntac proof tree datatype represents a
proof tree with nodes for hole, exact term, applications of tactic, and context
manipulation.

@defstruct[ntt ([contains-hole? boolean?] [goal syntax?]) #:transparent]{
An ntac proof tree. Records the current @racket[goal], as syntax representing a Cur type, and whether or not there is a hole.
}

@defstruct[(ntt-hole ntt) ([contains-hole? boolean?] [goal syntax?]) #:transparent]{
A node in an ntac proof tree representing a hole to be filled.
}

@defproc[(make-ntt-hole [goal syntax?]) ntt?]{
Create a new @racket[ntt-hole?] node whose hole is @racket[goal?].
The resulting @racket[ntt?] does @racket[contains-hole?].
}

@defstruct[(ntt-exact ntt) ([contains-hole? boolean?] [goal syntax?] [term syntax?]) #:transparent]{
A node in an ntac proof tree holding a Cur @racket[term], as @racket[syntax?], satisfying @racket[goal].
}

@defproc[(make-ntt-exact [goal syntax?] [term syntax?]) ntt?]{
Create a new @racket[ntt-exact?] node that proves @racket[goal] via the Cur
term @racket[term].
The resulting @racket[ntt?] does not @racket[contains-hole?].
}

@defstruct[(ntt-context ntt) ([contains-hole? boolean?] [goal syntax?] [env-transformer (-> dict? dict?)] [subtree ntt?]) #:transparent]{
A node in an ntac proof tree that records information about the local environment, by manipulating the context of the @racket[subtree] using @racket[env-transformer].
}

@defproc[(make-ntt-context [env-transformer (-> dict? dict?)] [subtree ntt?]) ntt?]{
Create a new @racket[ntt-context?] node that manipulates the @racket[subtree]
according to @racket[env-transformer].
The resulting @racket[ntt?] inherits the @racket[goal] from @racket[subtree] and
only @racket[contains-hole?] if @racket[subtree] does.
}

@defstruct[(ntt-apply ntt) ([contains-hole? boolean?] [goal syntax?] [subtrees (listof? ntt?)] [f (-> syntax? ... syntax?)]) #:transparent]{
A node in an ntac proof tree that proves @racket[goal] by using @racket[f] to combine the terms that result from @racket[subtrees] into a single Cur term.
}

@defproc[(make-ntt-apply [goal syntax?] [subtrees (listof? ntt)] [f (-> syntax? ... syntax?)]) ntt?]{
Create a new @racket[ntt-apply?] node that uses @racket[f] to build a proof tree out of @racket[subtrees], with @racket[goal] remaining to be proved.
The resulting @racket[ntt?] @racket[contains-hole?] if any @racket[subtrees] do.
}

@defstruct[(ntt-done ntt) ([contains-hole? boolean?] [goal syntax?] [subtree ntt?]) #:transparent]{
A node in an ntac proof tree that asserts that the @racket[subtree] is complete.
}

@defproc[(make-ntt-done [subtree ntt?]) ntt?]{
Create a new @racket[ntt-done?] node with @racket[subtree].
Results in an error if @racket[subtree] @racket[contains-hole?].
}

@defproc[(new-proof-tree [goal syntax?]) ntt?]{
Create a new proof tree with @racket[goal].
}

@section{Proof Tree Zipper}

To navigate the proof tree, we define a proof tree zipper.
@todo{Document zipper}


@todo{tactic system commands}