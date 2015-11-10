#lang scribble/manual

@(require "../defs.rkt")

@title{Tactics}
As Coq has shown, tactics have proven useful for doing complex proofs. In Cur, tactics are not
built-in or provided by the language. However, any user can use meta-programming to add tactics to
Cur. A tactic system ships in the standard library, written entirely in user-land code.

@(require racket/sandbox scribble/eval)
@(define curnel-eval
   (parameterize ([sandbox-output 'string]
                  [sandbox-error-output 'string]
                  [sandbox-eval-limits #f]
                  [sandbox-memory-limit #f])
     (make-module-evaluator "#lang cur (require cur/stdlib/tactics/base)  (require cur/stdlib/tactics/standard) (require cur/stdlib/bool) (require cur/stdlib/nat)")))

@section{Proof State and Defining Tactics}
@defmodule[cur/stdlib/tactics/base]

@defform*[((define-tactic (name id ... id-ps))
           (define-tactic name procedure-expr))]{
Defines a new @tech{tactic}, at @gtech{phase} 1. A @deftech{tactic} is a Racket function from
@tech{proof state} to @tech{proof state} that runs at @gtech{phase} 1. A @tech{tactic} takes any
number of arguments, plus the @tech{proof state}. The @tech{proof state} must be the final argument of
the tactic.

@examples[#:eval curnel-eval
(define-tactic (do-nothing ps)
  ps)
(define-tactic (switch-goal i ps)
  (struct-copy proof-state ps
    [current-goal i]))
]
}

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
A structure representing the @deftech{proof state} for the proof of the current theorem.

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

@defproc[(proof-state-goal-ref [ps proof-sate?] [i natural-number/c])
         syntax?]{
Returns the @racket[i]th @tech{goal} from the proof state @racket[ps].
}

@defproc[(proof-state-current-goal-ref [ps proof-state?])
         syntax?]{
Returns the @tech{goal} using the index from
@racket[(proof-state-current-goal ps)].
}

@defproc[(proof-state-env-ref [ps proof-state?] [name symbol?])
         syntax?]{
Returns the type of the assumption @racket[name] in the local
environment of @racket[ps].
}

@defproc[(proof-state-env-ref-by-type [ps proof-state?] [type syntax?])
         (or/c symbol? #f)]{
Returns the name of the assumption of type @racket[type] from the local
environment of @racket[ps], or @racket[#f] is no
assumption with @racket[type] exists.
}

@defproc[(proof-state-extend-env [ps proof-state?]
                                 [name (or/c symbol?  identifier?)]
                                 [type syntax?])
         proof-state?]{
Returns a proof state with the local environment of
@racket[ps] updated to include the assumption @racket[name] of type
@racket[type].
}

@defproc[(proof-state-current-goal-set [ps proof-state?]
                                       [goal syntax?])
         proof-state?]{
Returns a proof state with the current goal in the goals list of
@racket[ps] changed to @racket[goal].
}

@defproc[(proof-state-fill-proof-hole [ps proof-state?] [pf proof?])
         proof-state?]{
Returns a proof state with the current holes of the proof filled with
@racket[pf].
}

@defproc[(proof-state-extend-proof-context [ps proof-state?]
                                           [ctxt procedure?])
         proof-state?]{
Updates the proof in @racket[ps] by playing the current proof inside the
holes of @racket[ctxt].
}

@defproc[(print-proof-state [ps proof-state?])
         void?]{
Pretty-prints @racket[ps] to the @racket[current-output-port].
}

@defproc[(lookup-tactic [name (or/c symbol? identifier?)])
         procedure?]{
Returns the tactic defined with name @racket[name]. Only works when the
tactic is defined and a theorem has been defined but not proved.
}

@defform[(define-theorem name prop)]{
Defines a new theorem.
}

@defform[(proof (tactic args ...) ...)]{
Proves the theorem previously defined with @racket[define-theorem].  Currently, this proof is not
saved anywhere, only checked against the most recent theorem defined via @racket[define-theorem].

Note that the proof state is implicitly given to each call by @racket[proof] and should not appear as
an explicit argument.

@examples[#:eval curnel-eval
(define-theorem a-silly-theorem (forall (x : Nat) Nat))
(proof (intro x) (by-assumption))

(define-theorem falseo (forall (x : Type) x))
(eval:alts (proof (interactive)) (void))
]
}

@todo{Examples, better documentation (e.g. don't say "returns a proof state"; the signature says so)}

@section{Standard Tactics}
The tactic system includes several standard tactics.

@defmodule[cur/stdlib/tactics/standard]

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

@section{SarTactic (Sarcastic Tactics)}
@defmodule[cur/stdlib/tactics/sartactic]

The SarTactic library provides amusing wrappers around the standard tactics. This library exists
mostly for the author's own amusement, and to ensure the extensibility of the tactic system.

It defines the same tactics as @racketmodname[cur/stdlib/tactics/standard], but each tactics will
insult the user, and will only work some of the time.
