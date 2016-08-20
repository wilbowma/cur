#lang scribble/base
@(require
  scribble/manual
  scriblib/figure
  "defs.rkt"
  "bib.rkt")

@title*{Tactics}
In this section we describe a tactic system called @emph{ntac} implemented in
Cur.
We begin with an example of using the tactic system to prove a trivial theorem:
@racketblock[
ntac $ forall (A : Type) (a : A) A
  by-intro A
  by-intro b
  by-assumption
]
This example shows the type of the polymorphic identity function written using tactics.
In the first example, we use @racket[ntac], a form that builds an expression
given an initial goal followed by a tactic script.
This is similar to @code{Goal} in Coq, which introduces an anonymous goal and
can be followed by an Ltac script.
In this example, we use the @racket[by-intro] tactic, which takes a single optional argument
representing the name to bind as an assumption in the local proof environment,
to introduce the assumptions under arbitrary names.
Then, we conclude the proof with @racket[by-assumption], which takes no
arguments and searches the local environment for a term that matches the
current goal.
Since all goals are complete at this point, we end the proof.

@racketblock[
define-theorem id $ forall (A : Type) (a : A) A
  by-obvious
]
We can also use @racket[define-theorem] to define a new identifier using an ntac script.
This form is simple syntax sugar for @racket[(define id (ntac (forall (A :
Type) (a : A) A) (by-obvious)))].
In this example, we use the @racket[by-obvious] tactic which solves certain
trivial theorems.


We begin implementing this by implementing the @racket[ntac] form:
@RACKETBLOCK[
define-syntax (ntac stx)
  syntax-case stx ()
    [(_ goal . script) (ntac-interp #'goal #'script)]
]
The @racket[ntac] form runs, at compile-time, the Racket function @racket[ntac-interp] to generate a Cur term.
The function @racket[ntac-interp] takes syntax representing a Cur type,
@racket[#'goal] and syntax representing a sequence of tactics,
@racket[#'script], and interprets the script.

In ntac, Cur partial terms with multiple holes and contextual information such
as assumptions are represented by the ntac proof tree @racket[ntt], while
tactic navigate the tree to focus on a particular goal using the ntac proof
tree zipper @racket[nttz].
We represent tactics as metalanguage functions that take a zipper over a proof
tree, an @racket[nttz], and returns a modified @racket[nttz].
We will not discuss this design or these data structures in more details here;
the design is described in the Cur documentation.

Since tactics are just metalanguage functions, we can create syntactic sugar
for defining tactics as follows:
@racketblock[
define-syntax (define-tactic syn)
  syntax-rules ()
    [(_ e ...)
     (begin-for-syntax
       (define e ...))]
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
begin-for-syntax
  define (run-tactic ps t)
    syntax-case t ()
      (f args ...)
       apply $ eval #'f
         cons ps
           syntax->list #'(args ...)
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
begin-for-syntax
  define (run-tactic-script thm script)
    define ps
      for/fold ([ps (new-proof-state thm)])
               ([tactic script])
        run-tactic ps tactic
    check-final-proof-state theorem ps
    proof-state-proof ps
]
We begin by generating a fresh proof state whose initial goal is the theorem.
The @racket[for/fold] form folds @racket[run-tactic] over the list of tactic
calls with the initial proof state.
We check the final proof state against the original theorem, which either
raises an error or returns, then extract and return the proof.

We begin defining tactics with the @racket[intro] tactic seen in our earlier
example.
@RACKETBLOCK[
define-tactic (intro ps name)
  syntax-case (cur-expand (current-goal ps)) (:)
    [(Π (x : P) body)
     let* ([ps (extend-env ps name #'P)]
           [ps (set-current-goal ps #'body)]
           [ps (fill-hole ps
                 (new-hole x
                   #`(λ (#,name : P) #,x)))])
      ps]
    [_ (error 'intro "Goal not (Π (x : P) t)")]
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
define-tactic (by-assumption ps)
  define maybe-name
    env-ref-by-type ps $ current-goal ps
  unless maybe-name
    error 'by-assumption "No assumption"
  let ([ps (fill-hole ps maybe-name)])
    finish-current-goal ps
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
define-tactic (obvious ps)
  syntax-case (cur-expand (current-goal ps))
    [(Π (x : P) t) obvious (intro ps #'x)]
    [t (if (ref-by-type ps #'t)
          (by-assumption ps)
          (error 'obvious "Not obvious."))]
]
The @racket[obvious] tactic tries @racket[intro] and recurs until the goal does
not match a dependent function type.
Then it tries @racket[by-assumption].
Recall that we use unconditional errors as failures in tactics, so we must manually
check if a suitable assumption exists before trying @racket[by-assumption] in
order to provide a more appropriate error message.

As we have the entire metalanguage available, we can define sophisticated
tactics that do arbitrary metalanguage computation.
For instance, since our metalanguage provides I/O and reflection, we can define
interactivity as a user-defined tactic.
We begin implementing interactive by first implementing the @racket[print]
tactic.
This tactic will print the proof state and return it unmodified.
@racketblock[
define-tactic (print ps)
  printf "\n"
  for ([(k v) (in-dict (proof-state-env ps))])
    printf "~a : ~a\n" k v
  printf "--------------------------------\n"
  if $ proof-complete? ps
     printf "Goal complete!\n\n"
     printf "~a\n\n" $ current-goal ps
  ps
]
To print a proof state, we print each assumption in the local environment as
@racket[name : type].
Then we print a horizontal line followed by the current goal or "Goal
complete!" if the proof is finished.

Now we define @racket[interactive].
This tactic uses the @racket[print] tactic to print the proof state, then
starts a read-eval-print-loop (REPL).
@racketblock[
define-tactic (interactive ps)
  printf "Starting interactive session:\n"
  printf "Type (quit) to quit.\n"
  let loop ([ps ps] [cmds '()])
    print ps
    let ([cmd (read-syntax)])
      syntax-case cmd (quit)
        [(quit) ....]
        [(f args ...)
         (loop (run-tactic ps #'(f args ...))
               (cons cmd cmds))]
]
The REPL reads in a command and runs it via @racket[run-tactics] if it is a
tactic.
We collect each tactic call into a list to print the tactic script to the user
at the end of the session.
The REPL also accepts @racket[quit] as a command that exits the REPL, prints
the tactic script, and returns the final proof state.
Recall that syntax objects have location information attached, so we could in
principle write the tactic script directly to the source file.

Now we have defined not only a user-defined tactic system, but a user-defined
@emph{interactive} tactic system.
We can use the interactive tactic just like any other tactic:
@racketblock[
define-theorem id2 $ forall (A : Type) (a : A) A
proof (interactive)
]
The following is a sample session in our interactive tactic:
@racketblock[
Type (quit) to quit.

——————————–
(forall (A : Type) (forall (a : A) A))

> (intro A)
.....

a : A
A : Type
——————————–
Goal complete!

> (quit)
Your tactic script:
'((intro A) (intro a) (by-assumption))
]