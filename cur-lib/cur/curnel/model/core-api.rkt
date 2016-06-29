#lang racket/base

;; Additional API utilities for interacting with the core, but aren't necessary for the model of the core language.
(require
 "../snoc-env.rkt"
 (except-in
  "core.rkt"
  apply)
  redex/reduction-semantics)

(provide
 (except-out (all-from-out "core.rkt")
             instantiate)
 (all-defined-out))

(define x? (redex-match? ttL x))
(define t? (redex-match? ttL t))
(define e? (redex-match? ttL e))
(define U? (redex-match? ttL U))
(define Δ? (redex-match? ttL Δ))
(define Γ? (redex-match? tt-typingL Γ))
(define Ξ? (redex-match? tt-ctxtL Ξ))
(define Φ? (redex-match? tt-ctxtL Φ))
(define Θ? (redex-match? tt-ctxtL Θ))
(define Θv? (redex-match? tt-cbvL Θv))
(define E? (redex-match? tt-cbvL E))
(define v? (redex-match? tt-cbvL v))

(define-metafunction ttL
  subst-all : t (x ...) (e ...) -> t
  [(subst-all t () ()) t]
  [(subst-all t (x_0 x ...) (e_0 e ...))
   (subst-all (substitute t x_0 e_0) (x ...) (e ...))])

(define-metafunction ttL
  Δ-set : Δ x n t ((x : t) ...) -> Δ
  [(Δ-set Δ x n t any)
   (Δ (x : n t (snoc-env-build ∅ any)))])

(define-metafunction ttL
  Δ-union : Δ Δ -> Δ
  [(Δ-union Δ_0 Δ_1)
   (snoc-env-merge Δ_0 Δ_1)])

(define-metafunction tt-redL
  step : Δ e -> e
  [(step Δ e)
   ,(car (apply-reduction-relation (tt-->cbv (term Δ)) (term e)))])

(define-metafunction tt-typingL
  [(Γ-union Γ ∅) Γ]
  [(Γ-union Γ_2 (Γ_1 x : t))
   (Γ-set (Γ-union Γ_2 Γ_1) x t)])

(define-metafunction tt-typingL
  Γ-set : Γ x t -> Γ
  [(Γ-set Γ x t) (Γ x : t)])

;; NB: Depends on clause order
(define-metafunction tt-typingL
  Γ-remove : Γ x -> Γ
  [(Γ-remove ∅ x) ∅]
  [(Γ-remove (Γ x : t) x) Γ]
  [(Γ-remove (Γ x_0 : t_0) x_1) (Γ-remove Γ x_1)])


