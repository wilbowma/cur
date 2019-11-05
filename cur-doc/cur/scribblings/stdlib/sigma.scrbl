#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label (only-meta-in 0 cur/stdlib/sigma))
  (for-label cur/stdlib/sugar)
  (for-label (only-meta-in 0 cur/stdlib/equality))
  (for-label (only-meta-in 0 cur/stdlib/nat))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/equality cur/stdlib/sigma cur/stdlib/nat cur/stdlib/sugar)"))

@title{Dependent Pairs}
@defmodule[cur/stdlib/sigma]
This library defines the strong dependent pair datatype, @racket[Σ], and basic
operations and syntax sugar.

@deftogether[(@defthing[#:kind "1 parameter type" Σ0 (-> (A : (Type 0)) (P : (-> A (Type 0))) (Type 0))]
              @defthing[#:kind "constructor" pair0 (-> (A : (Type 0)) (P : (-> A (Type 0))) (a : A) (b : (P a)) (Σ0 A P))])]{
The strong dependent pair datatype, for universe @racket[(Type 0)]
}

@deftogether[(@defthing[#:kind "1 parameter type" Σ1 (-> (A : (Type 1)) (P : (-> A (Type 1))) (Type 1))]
              @defthing[#:kind "constructor" pair1 (-> (A : (Type 1)) (P : (-> A (Type 1))) (a : A) (b : (P a)) (Σ1 A P))])]{
The strong dependent pair datatype, for universe @racket[(Type 1)]
}

@defform*[((Σ (x : A) P)
           (Σ A P))]{
Syntactic sugar for writing @racket[Σ0] and @racket[Σ1].
Infers which constructor to use based on the universe level of @racket[A].
The syntax @racket[(Σ (x : A) P)] expands to @racket[(Σ A (λ (x : A) P))].

@examples[#:eval curnel-eval
          (Σ (x : Nat) (== Nat x 5))
          (Σ0 Nat (λ (x : Nat) (== Nat x 5)))]
}

@defform[(pair P a b)]{
Syntactic sugar for writing @racket[pair0] and @racket[pair1].
Infers the type annotation @racket[A] based on the type of @racket[a]
Also infers which constructor to use based on the universe level of @racket[A].

@examples[#:eval curnel-eval
          (pair (λ (x : Nat) (== Nat x 5)) 5 (refl Nat 5))]
}

@defproc[(fst0 [A (Type 0)] [P (-> A (Type 0))] [p (Σ0 A P)]) A]{
Takes the first projection of @racket[p].
}

@defproc[(fst1 [A (Type 1)] [P (-> A (Type 1))] [p (Σ1 A P)]) A]{
Like @racket[fst0] but for @racket[Σ1].
}

@defform[(fst p)]{
Syntactic sugar for @racket[fst0] and @racket[fst1], like @racket[pair].
Infers the type arguments @racket[A] and @racket[P] from @racket[p], and
expands to @racket[(fst0 A P p)] or @racket[(fst1 A P p)] depending on the
universe levels of the types.

@examples[#:eval curnel-eval
          (fst (pair (λ (x : Nat) (== Nat x 5)) 5 (refl Nat 5)))]
}

@defproc[(snd0 [A (Type 0)] [P (-> A (Type 0))] [p (Σ0 A P)]) (P (fst p))]{
Takes the second projection of @racket[p].
}

@defproc[(snd1 [A (Type 1)] [P (-> A (Type 1))] [p (Σ1 A P)]) (P (fst p))]{
Like @racket[snd0] but for @racket[Σ1].
}

@defform[(snd p)]{
Syntactic sugar for @racket[snd0] and @racket[snd1], like @racket[fst].

@examples[#:eval curnel-eval
          (snd (pair (λ (x : Nat) (== Nat x 5)) 5 (refl Nat 5)))]
}