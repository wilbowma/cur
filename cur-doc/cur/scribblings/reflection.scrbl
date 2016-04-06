#lang scribble/manual

@(require
   "defs.rkt"
   scribble/eval
   (for-label (only-in racket local-expand)))

@title{Reflection}
To support the addition of new user-defined language features, @racketmodname[cur] provides access to
various parts of the language implementation as Racket forms at @gtech{phase} 1.
The reflection features are @emph{unstable} and may change without warning.

The reflection API enforced type safety; all terms are first expanded, then
type checked, then reduced; individual API function may not complete this
route---e.g, cur-expand stops after expansion---but not API functions will
reduce before type checking, or type check before expansion.

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/bool cur/stdlib/nat)"))

@defproc[(declare-data! [name syntax?] [type syntax?] [constructor-map (listof (cons/c syntax? syntax?))])
         void?]{
Extends the global inductive declarations with a new inductive type
@racket[name] of type @racket[type], with constructors declared in
@racket[constructor-map]. Constructors should in order, with the 0th
constructor appearing at position 0 in the @racket[constructor-map].
}

@defproc[(call-local-data-scope [thunk (-> any?)])
         any?]{
Calls @racket[thunk] with a local scope for inductive declarations.
Once outside of this new scope, any inductive types declared via @racket[data]
or via @racket[declare-data!] will be forgotten.
}

@defform[(local-data-scope e)]{
Syntax that expands to @racket[(call-local-data-scope (thunk e))].
}

@todo{Actually, env could be any ordered dictionary...}
@defproc[(call-with-env [env (listof (cons/c syntax? syntax?))] [thunk (-> any?)])
         any?]{
Calls @racket[thunk] with the lexical environment extended by @racket[env].
@racket[env] should be in reverse dependency order; the 0th element of
@racket[env] may depend on the 1st, the 1st may depend on the 2nd, etc.
}

@defform[(with-env env e)]{
Syntax that expands to @racket[(call-with-env env (thunk e))].
}

@defproc[(cur-expand [syn syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()] [id identifier?] ...)
         syntax?]{
Expands the Cur term @racket[syn] until the expansion reaches a either @tech{Curnel form} or one of
the identifiers @racket[id]. See also @racket[local-expand].

If @racket[#:local-env] is specified, expands under an extended lexical environment via @racket[with-env].
@todo{Examples of #:local-env.}

@todo{Figure out how to get evaluator to pretend to be at phase 1 so these examples work properly.}

@margin-note{The examples in this file do not currently run in the REPL, but should work if used at
phase 1 in Cur.}

@examples[
(eval:alts (define-syntax-rule (computed-type _) Type) (void))
(eval:alts (cur-expand #'(λ (x : (computed-type bla)) x))
           (eval:result @racket[#'(λ (x : Type) x)] "" ""))
]
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
]
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
(eval:alts (cur-type-check? #'x #'Nat #:local-env (list (cons #'x #'Nat)))
           (eval:result @racket[#t] "" ""))
]
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
                                        ()
                                        (z (λ (x2 : Nat) (λ (ih-n2 : Nat) x2)))
                                        (s (s z)))] "" ""))
]
}

@defproc[(cur-equal? [e1 syntax?] [e2 syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         boolean?]{
Returns @racket[#t] if the Cur terms @racket[e1] and @racket[e2] and equivalent according to
equal modulo α and β-equivalence.

If @racket[#:local-env] is specified, runs under an extended lexical environment via @racket[with-env].
@examples[


(eval:alts (cur-equal? #'(λ (a : Type) a) #'(λ (b : Type) b))
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-equal? #'((λ (a : Type) a) Bool) #'Bool)
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-equal? #'(λ (a : Type) (sub1 (s z))) #'(λ (a : Type) z))
           (eval:result @racket[#f] "" ""))
]
}


@defproc[(cur->datum [s syntax?] [#:local-env env (listof (cons/c syntax? syntax?)) '()])
         (or/c symbol? list?)]{
Converts @racket[s] to a datum representation of the @tech{curnel form}, after expansion.

If @racket[#:local-env] is specified, runs under an extended lexical environment via @racket[with-env].
@examples[


(eval:alts (cur->datum #'(λ (a : Type) a))
           (eval:result @racket['(λ (a : (Unv 0) a))] "" ""))
]
}
