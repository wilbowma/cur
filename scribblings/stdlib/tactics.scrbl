#lang scribble/manual

@(require "../defs.rkt")

@title{Tactics}
As Coq has shown, tactics have proven useful for doing complex proofs. In Cur, tactics are not
built-in or provided by the language. However, any user can use meta-programming to add tactics to
Cur. A tactic system ships in the standard library, written entirely in user-land code.

@section{Proof State and Defining Tactics}
In Cur, a @deftech{tactic} is a Racket function from @tech{proof state} to @tech{proof state} that
runs at @gtech{phase} 1.

@defproc[(proof? [p any/c])
         boolean?]{
Returns @racket[#t] if @racket[p] is a proof, and @racket[#f] otherwise.
A @deftech{proof} is either a Cur term as a syntax object, or a procedure expecting a proof to plug
into the holes of the existing partial proof.
}

@defproc[(complete-proof? [p any/c])
         boolean?]{
Returns @racket[#t] is the proof @racket[p] has no holes, i.e., is a syntax object, and @racket[#f]
otherwise.
}

@defproc[(new-proof)
         proof?]{
Returns an empty partial @tech{proof}, i.e., the identity function.
}

@defstruct[proof-state ([env dict?]
                        [goals dict?]
                        [current-goal natural-number/c]
                        [proof (or/c syntax? procedure?)]
                        [theorem syntax?])]{
The environment @racket[env] is a map of assumptions local to the theorem from symbols (names) to the
type of the assumption as a syntax object.
The list of goals @racket[goals] is a map from natural numbers to goals, types as syntax objects.
The current goal @racket[current-goal] is a natural number indexing into @racket[goals], representing
the goal currently in focus.
The @racket[proof] is the @tech{proof} of the theorem so far. The @racket[proof] is either a
syntax object if complete, or a procedure which expects a proof to replace the current holes in the
@racket[proof].
The @racket[theorem] is the original statement of the theorem to be proved.
}

@defproc[(new-proof-state [prop syntax?])
         proof-state?]{
Returns a @racket[proof-state?] initialized with an empty environment, the list of goals initialized with
@racket[prop], the current-goal set to @racket[0], an empty proof via @racket[(new-proof)], and the
theorem set to @racket[prop].
}

@defproc[(proof-state-proof-complete? [ps proof-state?])
         boolean?]{
Returns @racket[#t] is the proof of the @racket[proof-state?] @racket[ps] is a
@racket[complete-proof?], and @racket[#f] otherwise.
}

@section{Standard Tactics}

@section{Interactive Tactic}

@section{SarTactic (Sarcastic Tactics)}
