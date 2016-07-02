#lang scribble/manual

@(require
  "../defs.rkt"
  scribble/eval)

@title{ntac--The New Tactic System}
@author[@author+email["William J. Bowman" "wjb@williamjbowman.com"]]
@author[@author["Jay McCarthy"]]

As Coq has shown, tactics have proven useful for doing complex proofs.
In Cur, tactics are not built-in or provided by the language.
However, any user can use meta-programming to add tactics to Cur.
In fact, a user did.
Cur originally shipped with a proof-of-concept tactic system, but the system did not scale well.
So Jay designed and prototyped a new one over a weekend in 200 lines of code.
Now it's the default system.

First we define the ntac proof tree datatype, which represents a proof tree with nodes for hole, exact term, applications of tactic, and context manipulation. 
Next we define a zipper over this proof tree for navigating the focus of the proof.
Then we can define tree navigating commands and hole filling tactics.

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/ntac/base cur/stdlib/ntac/standard cur/stdlib/bool cur/stdlib/nat)"))

@section{Proof Tree}
@defmodule[cur/stdlib/ntac/base]

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

@todo{Document zipper}

@todo{Document syntax, tactic system commands}

@todo{Document tactics}

@section{Standard Tactics}
The tactic system includes several standard tactics.

@defmodule[cur/stdlib/ntac/standard]

@defproc[(intro [name identifier?] [ps proof-state?])
         proof-state?]{
Matches when the current goal has the form @racket[(forall (id : type-expr) body-expr)], introducing
the assumption @racket[id : type-expr] into the local environment of @racket[ps].
}

@defproc[(by-assumption [ps proof-state?])
         proof-state?]{
Matches with the current goal has a type that matches an assumption in the local environment of
@racket[ps]. Completes the goal.
}

@defproc[(obvious [ps proof-state?])
         proof-state?]{
Attempts to prove the current goal by doing the obvious thing.
}

@defproc[(restart [ps proof-state?])
         proof-state?]{
Resets @racket[ps] to its state when the proof began. Clears the proof and goals, reinitializing the
goals to the original theorem.
}

@defproc[(print [ps proof-state?])
         proof-state?]{
Prints @racket[ps], returning it unmodified.
}

@defproc[(forget [x identifier?] [ps proof-state?])
         proof-state?]{
Removes the assumption @racket[x] from the local environment of @racket[ps].
}

@section{Interactive Tactic}
In Cur, interactivity is just a user-defined tactic.

@defproc[(interactive [ps proof-state?])
         proof-state?]{
Starts a REPL that prints @racket[ps], reads a tactic (as @racket[proof] would), evaluates the
tactic, and repeats. To quit, use @racket[(quit)].
}