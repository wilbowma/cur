#lang scribble/manual

@(require
  "../defs.rkt"
  (for-label (only-meta-in 0 cur/stdlib/equality))
  (for-label (only-meta-in 0 cur/stdlib/nat))
  (for-label (except-in cur/stdlib/sugar :))
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/nat cur/stdlib/sugar cur/stdlib/equality)"))

@title{Equality}
@defmodule[cur/stdlib/equality]
This library defines the Paulin-Mohring and Martin-Löf equality types.

@deftogether[(@defthing[#:kind "2 parameter type" PM-= (-> (A : Type) (x : A) (y : A) Type)]
              @defthing[#:kind "constructor" PM-refl (-> (A : Type) (x : A) (PM-= A x x))])]{
The Paulin-Mohring equality type (PM equality).
Also provided as @defidform/inline[==] and @defidform/inline[refl], as this
should be considered the default equality.

@examples[#:eval curnel-eval
          (:: (PM-refl Nat z) (PM-= Nat z z))
          (new-elim (PM-refl Nat z)
                    (lambda (x : Nat) (t : (PM-= Nat z x))
                      (PM-= Nat z z))
                    (PM-refl Nat z))
]
}

@defproc[(PM-sym [A Type] [n A] [m A] [n=m (PM-= A n m)]) (PM-= A m n)]{
A proof of symmetry for PM equality.
}

@defproc[(PM-trans [A Type] [a A] [b A] [c A] [H1 (PM-= A a b)] [H2 (PM-= A b c)]) (PM-= A a c)]{
A proof of transitivity for PM equality.
}

@deftogether[(@defthing[#:kind "1 parameter type" ML-= (-> (A : Type) (x : A) (y : A) Type)]
              @defthing[#:kind "constructor" ML-refl (-> (A : Type) (x : A) (PM-= A x x))])]{
The Martin-Löf equality type (ML equality).

@examples[#:eval curnel-eval
          (:: (ML-refl Nat z) (ML-= Nat z z))
          (new-elim (ML-refl Nat z)
                    (lambda (x : Nat) (y : Nat) (t : (ML-= Nat x y))
                      (ML-= Nat x y))
                    (lambda (x : Nat) (ML-refl Nat x)))
]
}