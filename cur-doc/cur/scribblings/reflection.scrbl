#lang scribble/manual

@(require
   "defs.rkt"
   scribble/eval
   racket/sandbox
   (for-label
     (only-in racket local-expand)))

@title{Reflection}
To support the addition of new user-defined language features, @racketmodname[cur] provides access to
various parts of the language implementation as Racket forms at @gtech{phase} 1.
The reflection features are @emph{unstable} and may change without warning.

The reflection API enforces type safety; all terms are first expanded, then
type checked, then reduced; individual API function may not complete this
route---e.g, cur-expand stops after expansion---but no API functions will
reduce before type checking, or type check before expansion.

@margin-note{Because these functions must be used during the dynamic extent of a syntax transformer application by the expander (see @racket[local-expand]), the examples in this file do not currently run in the REPL, so these examples may contain typos.}

@(define local-env-message @elem{a macro to delay the function call until the binder is expanded. See @racket[cur-type-infer] for an example.})

@;@(define cur-eval
@;  (parameterize ([sandbox-output 'string]
@;                 [sandbox-error-output 'string]
@;                 [sandbox-eval-limits '(30 256)]
@;                 [sandbox-memory-limit 256])
@;    (make-module-evaluator
@;     (format "#lang racket~n(require (for-template cur))~n"))))

@history[#:changed "0.20" @elem{Removed @racket[declare-data!], @racket[call-local-data-scope], @racket[local-data-scope]---we can't implement these in the new Curnel, and they were hacks to begin with.}]

@defproc[(call-with-env [env (listof (cons/c syntax? syntax?))] [thunk (-> any?)])
         any?]{
Calls @racket[thunk] with the lexical environment extended by @racket[env].
@racket[env] should be in reverse dependency order; the 0th element of

@racket[env] may depend on the 1st, the 1st may depend on the 2nd, etc.

@deprecated[#:what "function" @local-env-message]
}

@defform[(with-env env e)]{
Syntax that expands to @racket[(call-with-env env (thunk e))].

@deprecated[#:what "function" @local-env-message]
}

@defproc[(cur-expand [syn syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()] [id identifier?] ...)
         syntax?]{
Expands the Cur term @racket[syn] until the expansion reaches a either @tech{Curnel form} or one of
the identifiers @racket[id]. See also @racket[local-expand].

If @racket[#:local-env] is specified, expands under an extended lexical environment via @racket[with-env].

@todo{Figure out how to get evaluator to pretend to be at phase 1 so these examples work properly.}

@examples[
(eval:alts (define-syntax-rule (computed-type _) Type) (void))
(eval:alts (cur-expand #'(λ (x : (computed-type bla)) x))
           (eval:result @racket[#'(λ (x : Type) x)] "" ""))
]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}

@defproc[(cur-type-infer [syn syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         (or/c syntax? #f)]{
Returns the type of the Cur term @racket[syn], or @racket[#f] if no type could be inferred.

If @racket[#:local-env] is specified, infers types under an extended lexical environment via @racket[with-env].

@examples[
(eval:alts (cur-type-infer #'(λ (x : Type) x))
           (eval:result @racket[#'(Π (x : (Type 0)) (Type 0))] "" ""))
(eval:alts (cur-type-infer #'Type)
           (eval:result @racket[#'(Type 1)] "" ""))
(eval:alts (cur-type-infer #'X #:local-env '((#'X . #'(Type 0))))
           (eval:result @racket[#'(Type 0)] "" ""))
(eval:alts (define-syntax-rule (cur-type-infer& t) (cur-type-infer t))
           (void))
(eval:alts #`(λ (X : (Type 0)) (cur-type-infer& X))
           (eval:result @racket[#`(λ (X : (Type 0)) (cur-type-infer& X))] "" ""))
]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}

@defproc[(cur-type-check? [term syntax?] [type syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         boolean?]{
Returns @racket[#t] if the Cur term @racket[term] is well-typed with a subtype of @racket[type], or @racket[#f] otherwise.

If @racket[#:local-env] is specified, checks the type under an extended lexical environment via @racket[with-env].

@examples[
(eval:alts (cur-type-check? #'(λ (x : Type) x) #'(Π (x : (Type 1)) Type))
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-type-check? #'Type #'(Type 1))
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-type-check? #'x #'Nat)
           (eval:result @racket[#f] "" ""))
(eval:alts (cur-type-check? #'x #'Nat #:local-env `((#'x . #'Nat)))
           (eval:result @racket[#t] "" ""))

]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}

@defproc[(cur-reflect-id [id identifier?])
         identifier?]{
Return the original name of @racket[id] for identifiers that have been renamed during expansion or type-checking, if one exists.

@history[#:added "0.20"]
}

@defproc[(cur-rename [new identifier?] [old identifier?] [term syntax?])
         syntax?]{
Replace @racket[old] by @racket[new] in @racket[term], without evaluating or expanding @racket[term].
While @racket[cur-normalize] can be used to substitute into a term, @racket[cur-rename] can be useful when you want to keep a term in the surface syntax.

@examples[
(eval:alts (cur-rename #'Y #'X #'((λ (X : (Type 0)) X) X))
           #'((λ (X : (Type 0)) X) Y))
]

@history[#:added "0.20"]
}

@defproc[(cur-normalize [syn syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         syntax?]{
Runs the Cur term @racket[syn] to a value.

If @racket[#:local-env] is specified, runs under an extended lexical environment via @racket[with-env].

@examples[
(eval:alts (cur-normalize #'((λ (x : Type) x) Bool))
           (eval:result @racket[#'Bool] "" ""))
(eval:alts (cur-normalize #'(sub1 (s (s z))))
           (eval:result @racket[#'(s z)] "" ""))
]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}

@defproc[(cur-step [syn syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         syntax?]{
Runs the Cur term @racket[syn] for one step.

If @racket[#:local-env] is specified, runs under an extended lexical environment via @racket[with-env].

@examples[
(eval:alts (cur-step #'((λ (x : Type) x) Bool))
           (eval:result @racket[#'Bool] "" ""))
(eval:alts (cur-step #'(sub1 (s (s z))))
           (eval:result @racket[#'(elim Nat (λ (x2 : Nat) Nat)
                                        (z (λ (x2 : Nat) (λ (ih-n2 : Nat) x2)))
                                        (s (s z)))] "" ""))
]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}

@defproc[(cur-equal? [e1 syntax?] [e2 syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         boolean?]{
Returns @racket[#t] if the Cur terms @racket[e1] and @racket[e2] and equivalent according to
equal modulo α and β-equivalence.

If @racket[#:local-env] is specified, runs under an extended lexical environment via @racket[with-env].
@examples[
(eval:alts (cur-equal? #'(λ (a : (Type 0)) a) #'(λ (b : Type) b))
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-equal? #'((λ (a : (Type 0)) a) Bool) #'Bool)
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-equal? #'(λ (a : (Type 0)) (sub1 (s z))) #'(λ (a : (Type 0)) z))
           (eval:result @racket[#f] "" ""))
]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}


@defproc[(cur->datum [s syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         (or/c symbol? list?)]{
Converts @racket[s] to a datum representation of the @tech{curnel form}, after expansion.

If @racket[#:local-env] is specified, runs under an extended lexical environment via @racket[with-env].
@examples[
(eval:alts (cur->datum #'(λ (a : (Type 0)) a))
           (eval:result @racket['(λ (a : (Type 0)) a)] "" ""))
]

@deprecated[#:what "#:local-env keyword argument" @local-env-message]
}

@defproc[(cur-constructors-for [D identifier?])
         (listof identifier?)]{
Returns a list of constructors for the inductively defined type @racket[D].

@examples[
(eval:alts (cur-constructors-for #'Nat)
           (eval:result @racket['(#'z #'s)] "" ""))
]
}

@defproc[(cur-data-parameters [D identifier?])
         natural-number?]{
Return the number of invariant parameters for the inductively defined type @racket[D].

@examples[
(eval:alts (cur-data-parameters #'Nat)
           (eval:result @racket[0] "" ""))
(eval:alts (cur-data-parameters #'List)
           (eval:result @racket[1] "" ""))
]
}

@defproc[(cur-method-type [target syntax?] [motive syntax?])
         syntax?]{
Given an a @racket[target] (a constructor for some type @racket[D] applied to
its invariant parameters) and a @racket[motive] for eliminating it, return the
type of the method required for this constructor when eliminating @racket[D].
}

@defproc[(cur-constructor-telescope-length [c identifier?])
         natural-number?]{
Return the number of arguments to the constructor @racket[c].

@examples[
(eval:alts (cur-constructor-telescope-length #'z)
           (eval:result @racket[0] "" ""))
(eval:alts (cur-constructor-telescope-length #'s)
           (eval:result @racket[1] "" ""))
(eval:alts (cur-constructor-telescope-length #'cons)
           (eval:result @racket[3] "" ""))
]
}

@defproc[(cur-constructor-recursive-index-ls [c identifier?])
         (listof natural-number?)]{
Return a 0-indexed list of the positions of the recursive arguments of constructor @racket[c].

@examples[
(eval:alts (cur-constructor-recursive-index-ls #'z)
           (eval:result @racket['()] "" ""))
(eval:alts (cur-constructor-recursive-index-ls #'s)
           (eval:result @racket['(0)] "" ""))
(eval:alts (cur-constructor-recursive-index-ls #'cons)
           (eval:result @racket['(2)] "" ""))
]
}