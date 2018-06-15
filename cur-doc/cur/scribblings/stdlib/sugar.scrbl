#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label cur/stdlib/sugar)
  (for-label (only-meta-in 0 cur/stdlib/bool))
  (for-label (only-meta-in 0 cur/stdlib/nat))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/nat cur/stdlib/bool cur/stdlib/sugar cur/stdlib/list)"))


@title{Sugar}
The @tech{curnel forms} are sort of terrible for actually writing code. Functions and applications are
limited to single artity. Functions type must be specified using the dependent @racket[forall], even
when the dependency is not used. Inductive elimination can only be done via the primitive eliminator
and not via pattern matching. However, with the full force of Racket's syntactic extension system, we
can define not only simply notation, but redefine what application means, or define a pattern matcher
that expands into the eliminator.

@defmodule[cur/stdlib/sugar]
This library defines various syntactic extensions making Cur easier to write than writing raw TT.

@defform*[((Type n)
           Type)]{
Added @racket[Type] as a synonym for @racket[(Type 0)].

@history[#:changed "0.20" @elem{Moved @racket[Type] synonym from Curnel.}]
}

@defform[(-> decl decl ... type)
	  #:grammar
	  [(decl
	     type
	     (code:line (identifier : type)))]]{
A multi-artiy function type that supports dependent and non-dependent type declarations and automatic currying.
Also exported as the following names, because there are lots of synonyms in the literature:
@defidform/inline[→],
@defidform/inline[forall],
@defidform/inline[∀],
@defidform/inline[Pi],
@defidform/inline[Π].

@examples[#:eval curnel-eval
          (data And : 2 (-> Type Type Type)
            (conj : (-> (A : Type) (B : Type) A B ((And A) B))))
          ((((conj Bool) Bool) true) false)]

@examples[#:eval curnel-eval
          (data And : 2 (forall Type Type Type)
            (conj : (forall (A : Type) (B : Type) A B (And A B))))
          ((((conj Bool) Bool) true) false)]

}

@defform[(lambda (a : t) ... body)]{
Defines a multi-arity procedure that supports automatic currying.
Also provied as @defidform/inline[λ].

@examples[#:eval curnel-eval
          ((lambda (x : Bool) (lambda (y : Bool) y)) true)
          ((lambda (x : Bool) (y : Bool) y) true)
          ]
}

@defform[(#%app f a ...)]{
Defines multi-arity procedure application via automatic currying.

@examples[#:eval curnel-eval
          (data And : 2 (-> Type Type Type)
	    (conj : (-> (A : Type) (B : Type) A B ((And A) B))))
          (conj Bool Bool true false)]
}

@defform[(: name type)]{
Declare that the @emph{function} which will be defined as @racket[name] has type @racket[type].
Must precede the definition of @racket[name].
@racket[type] must expand to a function type of the form @racket[(Π (x : t1) t2)]
When used, this form allows omitting the annotations on arguments in the definition @racket[name]
}

@defform*[((define name body)
           (define (name x ...) body)
	   (define (name (x : t) ...) body))]{
Like the @racket[define] provided by @racketmodname[cur], but supports
defining curried functions via @racket[lambda].
The second form, @racket[(define (name x ...) body)], can only be used when
a @racket[(: name type)] form appears earlier in the module.
Also record @racket[name] in the transformer environment.

@examples[#:eval curnel-eval
          (: id (forall (A : Type) (a : A) A))
	  (define (id A a) a)]
}

@defform*[((define-type name type)
           (define-type (name (a : t) ...) body))]{
Like @racket[define], but uses @racket[forall] instead of @racket[lambda].
}

@defform[(match e [maybe-in] [maybe-return] [pattern body] ...)
         #:grammar
         [(maybe-in
	    (code:line #:in type))
	  (maybe-return
	    (code:line #:return type))
	  (pattern
            constructor
            (code:line (constructor x ...))
            (code:line (constructor (x : t) ...)))]]{
A pattern-matcher for inductive types.
Match clauses must begin with the constructor name, and be followed by all
indices and constructor arguments as pattern variable.
Match clauses can be given in any order.

Pattern variables do not need to be annotated, as the `match` form can infer their types.
If pattern variables are annotated, then the `match` form will ensure the
annotation matches the expected type before elaborating.

If `match` is used under a `define`, `match` can be used to define simple
primitive recursive functions, defined by induction on their first argument.

Inside the @racket[body], @racket[recur] can be used to refer to the
inductive hypotheses for an inductive argument.
Generates a call to the inductive eliminator for @racket[e].
Currently does not work on inductive type-families as types indices
are not inferred.

If @racket[#:in] is not specified, attempts to infer the type of @racket[e].
If @racket[#:return] is not specified, attempts to infer the return type of the @racket[match].

@examples[#:eval curnel-eval
          (match z
            [z true]
            [(s (n : Nat))
             false])]

@examples[#:eval curnel-eval
          (match z
            [(s n)
             false]
             [z true])]

@examples[#:eval curnel-eval
          (match (s z)
	    #:in Nat
	    #:return Bool
            [z true]
            [(s n)
            (not (recur n))])]

@examples[#:eval curnel-eval
          (define (+ (n : Nat) (m : Nat))
            (match n
              [z m]
              [(s n) (s (+ n m))]))]

@examples[#:eval curnel-eval
          ((match (nil Bool)
            [nil
	     (lambda (n : Nat)
	       (none A))]
            [(cons (a : Bool) (rest : (List Bool)))
	     (lambda (n : Nat)
	       (match n
	         [z (some Bool a)]
		 [(s (n-1 : Nat))
		  ((recur rest) n-1)]))])
	   z)]

}

@defform[(recur id)]{
A form valid only in the body of a @racket[match] clause.
Generates a reference to the induction hypothesis for @racket[x]
inferred by a @racket[match] clause.
}

@defform[(let (clause ...) body)
         #:grammar
         [(clause
            (code:line (id expr))
            (code:line ((id : type) expr)))]]{
Evaluates the expressions @racket[expr] from each clause, left to right, and binds them to each
@racket[id]. If a @racket[type] is not given for the @racket[id], attempts to infer the type of the
corresponding @racket[expr], raising a syntax error if no type can be inferred.

@examples[#:eval curnel-eval
          (let ([x Type]
                [y (λ (x : (Type 1)) x)])
            (y x))
          (let ([x uninferrable-expr]
                [y (λ (x : (Type 1)) x)])
            (y x))]
}

@defform[(:: e type)]{
Check that expression @racket[e] has type @racket[type], causing a type-error if not, and producing
@racket[(void)] if so.

@examples[#:eval curnel-eval
          (:: z Nat)
          (:: true Nat)]
}

@defform[(run syn)]{
Like @racket[cur-normalize], but is a syntactic form to be used in surface syntax.
Allows a Cur term to be written by computing part of the term from
another Cur term.

@examples[#:eval curnel-eval
          (lambda (x : (run (if true Bool Nat))) x)]

}

@defform[(step syn)]{
Like @racket[run], but uses @racket[cur-step] to evaluate only one step and prints intermediate
results before returning the result of evaluation.

@examples[#:eval curnel-eval
          (step (plus z z))]

@history[#:changed "0.20" "Broken by new Curnel; fix is part of planned rewrite of evaluator."]
}

@defform[(step-n natural syn)]{
Like @racket[step], but expands to @racket[natural] calls to @racket[step].

@examples[#:eval curnel-eval
          (step-n 3 (plus z z))]

@history[#:changed "0.20" "Broken by new Curnel; fix is part of planned rewrite of evaluator."]
}

@defform[(query-type expr)]{
Print the type of @racket[expr], at compile-time. Similar to Coq's @racketfont{Check}.

@examples[#:eval curnel-eval
          (query-type Bool)]

}
