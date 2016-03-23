#lang scribble/manual

@(require
   "defs.rkt"
   scribble/eval
   (for-label (only-in racket local-expand)))

@title{Reflection}
To support the addition of new user-defined language features, @racketmodname[cur] provides access to
various parts of the language implementation as Racket forms at @gtech{phase} 1.
The reflection features are @emph{unstable} and may change without warning.
Many of these features are extremely hacky.

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/bool cur/stdlib/nat)"))

@defproc[(cur-expand [syn syntax?] [id identifier?] ...)
         syntax?]{
Expands the Cur term @racket[syn] until the expansion reaches a either @tech{Curnel form} or one of
the identifiers @racket[id]. See also @racket[local-expand].

@todo{Figure out how to get evaluator to pretend to be at phase 1 so these examples work properly.}

@margin-note{The examples in this file do not currently run in the REPL, but should work if used at
phase 1 in Cur.}

@examples[
(eval:alts (define-syntax-rule (computed-type _) Type) (void))
(eval:alts (cur-expand #'(λ (x : (computed-type bla)) x))
           (eval:result @racket[#'(λ (x : Type) x)] "" ""))
]
}

@defproc[(cur-type-infer [syn syntax?])
         (or/c syntax? #f)]{
Returns the type of the Cur term @racket[syn], or @racket[#f] if no type could be inferred.

@examples[
(eval:alts (cur-type-infer #'(λ (x : Type) x))
           (eval:result @racket[#'(Π (x : (Type 0)) (Type 0))] "" ""))
(eval:alts (cur-type-infer #'Type)
           (eval:result @racket[#'(Type 1)] "" ""))
]
}

@defproc[(cur-type-check? [syn syntax?])
         boolean?]{
Returns @racket[#t] if the Cur term @racket[syn] is well-typed, or @racket[#f] otherwise.

@examples[
(eval:alts (cur-type-check? #'(λ (x : Type) x))
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-type-check? #'Type)
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-type-check? #'x)
           (eval:result @racket[#f] "" ""))
]
}

@defproc[(cur-normalize [syn syntax?])
         syntax?]{
Runs the Cur term @racket[syn] to a value.

@examples[
(eval:alts (cur-normalize #'((λ (x : Type) x) Bool))
           (eval:result @racket[#'Bool] "" ""))
(eval:alts (cur-normalize #'(sub1 (s (s z))))
           (eval:result @racket[#'(s z)] "" ""))
]
}

@defproc[(cur-step [syn syntax?])
         syntax?]{
Runs the Cur term @racket[syn] for one step.

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

@defproc[(cur-equal? [e1 syntax?] [e2 syntax?])
         boolean?]{
Returns @racket[#t] if the Cur terms @racket[e1] and @racket[e2] and equivalent according to
equal modulo α and β-equivalence.
@examples[


(eval:alts (cur-equal? #'(λ (a : Type) a) #'(λ (b : Type) b))
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-equal? #'((λ (a : Type) a) Bool) #'Bool)
           (eval:result @racket[#t] "" ""))
(eval:alts (cur-equal? #'(λ (a : Type) (sub1 (s z))) #'(λ (a : Type) z))
           (eval:result @racket[#f] "" ""))
]
}


@defproc[(cur->datum [s syntax?])
         (or/c symbol? list?)]{
Converts @racket[s] to a datum representation of the @tech{curnel form}, after expansion.
@examples[


(eval:alts (cur->datum #'(λ (a : Type) a))
           (eval:result @racket['(λ (a : (Unv 0) a))] "" ""))
]
}
