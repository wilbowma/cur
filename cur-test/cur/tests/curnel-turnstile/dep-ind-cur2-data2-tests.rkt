#lang s-exp cur/curnel/turnstile-impl/dep-ind-cur2
(require cur/curnel/turnstile-impl/dep-ind-cur2+sugar
         cur/curnel/turnstile-impl/dep-ind-cur2+data2
         rackunit/turnstile)

;; define-datatype TODO:
;; - not specifying constructors results in define-red err

;; error description: same binder for param and index
;; data1 err: stx parse dup attr
;; (require "../dep-ind-cur2+data2.rkt")
#;(define-datatype T [A : Type] : [A : Type] -> Type
  [C : (∀ [A : Type] [B : Type] (T A B))])

;; data2 err: stx parse dup attr
#;(define-datatype T [A : Type] : [A : Type] -> Type
  [C : [B : Type] -> (T A B)])

;; error description: constructor re-binds param
;; data2 err: stx parse dup attr
#;(define-datatype T [A : Type] : [B : Type] -> Type
  [C : [A : Type] -> (T A A)])

;; error description: A : A
#;(define-datatype T [A : A] : -> Type
  [C : (T A)])

;(C Type) ; data2 err: expected T given A
;(T Type)  ; data2 err: expected Type 1, given Type

;; ;; error description: another binder uses A
;; (define-datatype TY [A : (Π [A : Type] Type)] : -> Type
;;   [C : (TY A)])

;; (check-type (C (λ [x : Type] x)) : (TY (λ [x : Type] x)))

;; ;; data2 err: A gets subst with arg, eg (Π [(λ [x : Type] x) : Type] Type)
;; ;; due to pattern-var-sub trick, use expanded/fresh vars to avoid this
;; (check-type (TY (λ [x : Type] x)) : Type) ; BAD ; 2018-06-24: fixed

;; (check-type (λ [x : Type]  x) : (Π [A : Type] Type))
