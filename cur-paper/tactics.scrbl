#lang scribble/base
@(require
  scribble/manual
  scriblib/figure
  "defs.rkt"
  "bib.rkt")

@title*{Tactics}
In this section we describe a proof-of-concept tactic system implemented in
Cur.
We begin with an example of using the tactic system to prove a trivial theorem:
@racketblock[
(define-theorem id0 (forall (A : Type) (a : A) A))
(proof
  (intro A)
  (intro b)
  (by-assumption))

(define-theorem id1 (forall (A : Type) (a : A) A))
(proof (obvious))
]
This example shows the type of the polymorphic identity function written as a
theorem.
In this tactic system, theorems are Cur types and must be defined using the
@racket[define-theorem] form.
After a @racket[define-theorem] form, we can use the @racket[proof] form to
begin a tactic script and use tactics to write a term that inhabits the type
declare in the preceding @racket[define-theorem].
The tactic script is a sequence of tactics applied to their arguments.

In this example, we use the @racket[intro] tactic, which takes a single argument
representing the name to bind as an assumption in the local proof environment,
to introduce the assumptions under arbitrary names.
Then, we conclude the proof with @racket[by-assumption], which takes no
arguments and searches the local environment for a term that matches the
current goal.
Since all goals are complete at this point, we end the proof.

We could alternatively have used the @racket[obvious] tactic, which solves
certain trivial theorems.

We begin implementing this by implementing the @racket[define-theorem] and
@racket[proof] forms:
@RACKETBLOCK[
(define-syntax (define-theorem syn)
  (syntax-case syn ()
    [(_ name prop)
     (begin
       (set-current-theorem #'prop)
       (set-current-theorem-name #'name)
       #'(void))]))

(define-syntax (proof syn)
  (syntax-case syn ()
    [(_ (f args ...) ...)
     #`(define #,(get-current-theorem-name)
         #,(run-tactic-script
             (get-current-theorem)
             (syntax->list #'((f args ...) ...))))]))
]
The @racket[define-theorem] form uses the functions
@racket[set-current-theorem] and @racket[set-current-theorem-name] to store the
theorem and name that will be used by the @racket[proof] form.
The @racket[proof] form we generates a definition by using the stored theorem
name and running the tactic script using the metalanguage function
@racket[run-tactic-script], which takes a the theorem as a goal and the take
script to run.

We choose this imperative design intentionally to demonstrate accumulating
state across multiple forms, and to model Coq's theorem/proof syntax.
A better design would allow using tactic scripts in arbitrary expression
contexts rather than only after a @racket[define-theorem].
We could easily support this by, for instance, changing the @racket[proof] form
to take a goal as an argument.
@todo{Perhaps implement this version for the next version of the paper}

In this tactic system, we represent tactics as metalanguage functions that take
a proof state and an arbitrary number of other arguments.
Since tactics are just metalanguage functions, we can create syntactic sugar
for defining tactics as follows:
@racketblock[
(define-syntax (define-tactic syn)
  (syntax-rules ()
    [(_ e ...)
     (begin-for-syntax
       (define e ...))]))
]
The form @racket[define-tactic] is simply a wrapper for conveniently
defining a new metalanguage function.
Note that this extension generates metalanguage code, by generating a new
metalanguage block containing a metalanguage definition.
Until now, we have only seen extensions that compute using the metalanguage and
generate code in object language, but recall from @secref{sec:cur} that Cur
supports an infinite hierarchy of language extension.

Now let us write the tactic script interpreter.
We begin by defining the function @racket[run-tactic], which takes a proof
state and a syntax object representing a call to a tactic as written by the
user.
@racketblock[
(begin-for-syntax
  (define (run-tactic ps t)
    (syntax-case t ()
      [(f args ...)
       (apply (eval #'f)
         (cons ps
           (syntax->list #'(args ...))))])))
]
We use @racket[eval] to evaluate the syntax representing the function name and
get a function value.
We convert the syntax representing the list of arguments to a list of arguments.
We leave each individual argument as a syntax object for the tactic to
interpret.
Since users do not write proof states directly, we then add the proof state to
the list of arguments.
Then we apply the function to the list of arguments using @racket[apply].

Finally, we define @racket[run-tactic-script] to run entire tactic scripts.
@racketblock[
(begin-for-syntax
  (define (run-tactic-script thm script)
    (define ps
      (for/fold ([ps (new-proof-state thm)])
                ([tactic script])
        (run-tactic ps tactic)))
    (check-final-proof-state theorem ps)
    (proof-state-proof ps)))
]
We begin by generating a fresh proof state whose initial goal is the theorem.
The @racket[for/fold] form folds @racket[run-tactic] over the list of tactic
calls with the initial proof state.
We check the final proof state against the original theorem, which either
raises an error or returns, then extract and return the proof.

We begin defining tactics with the @racket[intro] tactic seen in our earlier
example.
@RACKETBLOCK[
(define-tactic (intro ps name)
  (syntax-case (cur-expand (current-goal ps)) (:)
    [(Π (x : P) body)
     (let* ([ps (extend-env ps name #'P)]
            [ps (set-current-goal ps #'body)]
            [ps (fill-hole ps
                  (new-hole x
                    #`(λ (#,name : P) #,x)))])
       ps)]
    [_ (error 'intro "Goal not (Π (x : P) t)")]))
]
In @racket[intro], we start by expanding the current goal into a Curnel form,
so we do not need to consider arbitrary syntax sugar.
If the goal has the form of a dependent function type, we add the assumption
to the local environment of the proof state under the user provided name.
We replace the current goal with the body of the function type, and replace the
current proof hole with a function whose body contains a new hole.
If the goal does not have the right form, we raise an error.
Note that raising an error may not be a good idea for failures in tactics; a
better design might use exceptions or a failure monad instead.

Next we define @racket[by-assumption].
@racketblock[
(define-tactic (by-assumption ps)
  (define maybe-name
    (env-ref-by-type ps (current-goal ps)))
  (unless maybe-name
    (error 'by-assumption "No assumption"))
  (let ([ps (fill-hole ps maybe-name)])
    (finish-current-goal ps)))
]
We look for an assumption whose type matches the current goal.
If we do not find a matching assumption, we raise an error.
Otherwise, we fill the current goal with a reference to the matching name and
complete the goal.

Since tactics are arbitrary metalanguage functions, we can define tactics in
terms of other tactics, define recursive tactics, and even call to external
programs or solvers through the foreign-function interface of our metalanguage.
Our next tactic, @racket[obvious], demonstrates these first two features.
It will solve any theorem that follows immediately from its premises.
@racketblock[
(define-tactic (obvious ps)
  (syntax-case (cur-expand (current-goal ps))
    [(Π (x : P) t) (obvious (intro #'x ps))]
    [t (if (ref-by-type ps #'t)
           (by-assumption ps)
           (error 'obvious "Not obvious."))]))
]
The @racket[obvious] tactic tries @racket[intro] and recurs until the goal does
not match a dependent function type.
Then it tries @racket[by-assumption].
Recall that we use unconditional errors as failures in tactics, so we must manually
check if a suitable assumption exists before trying @racket[by-assumption] in
order to a more appropriate error message.

As we have the entire metalanguage available, we can define sophisticated
tactics that do arbitrary metalanguage computation.
For instance, since our metalanguage provides I/O and reflection, we can define
interactivity as a user-defined tactic.
We being implementing interactive by first implementing the @racket[print]
tactic.
This tactic will print the proof state and return it unmodified.
@racketblock[
(define-tactic (print ps)
  (printf "\n")
  (for ([(k v) (in-dict (proof-state-env ps))])
    (printf "~a : ~a\n" k v))
  (printf "--------------------------------\n")
  (if (proof-complete? ps)
      (printf "Goal complete!\n\n")
      (printf "~a\n\n" (current-goal ps)))
  ps)
]
To print a proof state, we print each assumption in the local environment as
@racket[name : type].
Then we print a horizontal line followed by the current goal or "Goal
complete!" if the proof is finished.

Now we define @racket[interactive].
This tactic uses the @racket[print] tactic to print the proof state, then
starts a read-eval-print-loop (REPL).
@racketblock[
(define-tactic (interactive ps)
  (printf "Starting interactive session:\n")
  (printf "Type (quit) to quit.\n")
  (let loop ([ps ps] [cmds '()])
    (print ps)
    (let ([cmd (read-syntax)])
      (syntax-case cmd (quit)
        [(quit) ....]
        [(f args ...)
         (loop (run-tactic ps #'(f args ...))
               (cons cmd cmds))]))))
]
The REPL reads in a command and runs it via @racket[run-tactics] if it is a
tactic.
We collect each tactic call into a list to print the tactic script to the user
at the end of the session.
The REPL also accepts @racket[quit] as a command that exits the REPL, prints
the tactic script, and returns the final proof state.
Recall that syntax objects have location information attached, so we could in
principle write the tactic script to directly source file.

Now we have defined not only a user-defined tactic system, but a user-defined
@emph{interactive} tactic system.
We can use the tactic just like other tactic:
@racketblock[
(define-theorem id2 (forall (A : Type) (a : A) A))
(proof (interactive))
]
The following is a sample session in our interactive tactic:
@racketblock[
Type (quit) to quit.

——————————–
(forall (A : Type) (forall (a : A) A))

> (intro A)
.....
> (by-assumption)

a : A
A : Type
——————————–
Goal complete!

> (quit)
Your tactic script:
'((intro A) (intro a) (by-assumption))
]