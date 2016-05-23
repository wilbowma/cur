#lang racket/base

(require
 racket/function
 racket/list
 scribble/base
 (except-in cur/curnel/model/core apply)
 redex/reduction-semantics
 [rename-in
  redex/pict
  (render-term _render-term)
  (render-language _render-language)
  (render-judgment-form _render-judgment-form)
  (render-reduction-relation _render-reduction-relation)]
 pict)

(provide
 (all-defined-out)
 #;(except-out
  (all-from-out redex/pict)
  render-term)
 (all-from-out
  redex/pict
  cur/curnel/model/core
  pict))

(default-font-size 9)
(metafunction-font-size 9)
(label-font-size 9)
(define (wrap bla)
  (with-compound-rewriters
    (['type-infer
      (lambda (lws)
        (define-values (Δ Γ e t)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)
           (list-ref lws 5)))
        (list "" Δ ";" Γ " ⊢ " e " ⇒ " t ""))]
     ['type-infer-normal
      (lambda (lws)
        (define-values (Δ Γ e t)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)
           (list-ref lws 5)))
        (list "" Δ ";" Γ " ⊢ " e " ⇒ " t ""))]
     ['type-check
      (lambda (lws)
        (define-values (Δ Γ e t)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)
           (list-ref lws 5)))
        (list "" Δ ";" Γ " ⊢ " e " ⇐ " t ""))]
     ['wf
      (lambda (lws)
        (define-values (Δ Γ)
          (values
           (list-ref lws 2)
           (list-ref lws 3)))
        (list "" " ⊨ " Δ ";" Γ ""))]
     ['substitute
      (lambda (lws)
        (define-values (e1 x e2)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)))
        (list "" e1 "[" x " / " e2 "]" ""))]
     ['subtype
      (lambda (lws)
        (define-values (Δ Γ t1 t2)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)
           (list-ref lws 5)))
        (list "" Δ ";" Γ " ⊢ " t1 " ≼ " t2 ""))]
     ['convert
      (lambda (lws)
        (define-values (Δ Γ t1 t2)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)
           (list-ref lws 5)))
        (list "" Δ ";" Γ " ⊢ " t1 " ≡ " t2 ""))]
     ['elim
      (lambda (lws)
        (define-values (elim D motive indices methods e)
          (values
           (list-ref lws 1)
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)
           (list-ref lws 5)
           (list-ref lws 6)))
        (list "" "(" elim (struct-copy lw D
                                       [e (text (format "~a" (lw-e D)) (non-terminal-subscript-style))]
                                       [column (sub1 (lw-column D))]) " " motive indices methods e ")" ""))]
     ['Δ-type-in
      (lambda (lws)
        (define-values (Δ D t)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)))
        (list "" "(" D ":" t ") ∈ " (struct-copy lw Δ [column (add1 (lw-column t))]) ""))]
     ['Δ-constr-in
      (lambda (lws)
        (define-values (Δ c t)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)))
        (list "" "(" c ":" t ") ∈ " (struct-copy lw Δ [column (add1 (lw-column t))]) ""))]
     ['Γ-in
      (lambda (lws)
        (define-values (Γ x t)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)))
        (list "" "(" x ":" t ") ∈ " (struct-copy lw Γ [column (add1 (lw-column t))]) ""))]
     ['unv-type
      (lambda (lws)
        (define-values (U1 U2)
          (values
           (list-ref lws 2)
           (list-ref lws 3)))
        (list "" "(" U1 ", " U2 ") ∈ A" ""))]
     ['unv-pred
      (lambda (lws)
        (define-values (U1 U2 U3)
          (values
           (list-ref lws 2)
           (list-ref lws 3)
           (list-ref lws 4)))
        (list "" "(" U1 ", " U2 ", " U3 ") ∈ R" ""))]
     ['Unv
      (lambda (lws)
        (define-values (unv i)
          (values
           (list-ref lws 1)
           (list-ref lws 2)))
        (list "" "(Type " i ")" ""))]
     ['<=
      (lambda (lws)
        (define-values (i0 i1)
          (values
           (list-ref lws 2)
           (list-ref lws 3)))
        (list "" i0 " ≤ " i1 ""))]
     ['max
      (lambda (lws)
        (define-values (max i0 i1)
          (values
           (list-ref lws 1)
           (list-ref lws 2)
           (list-ref lws 3)))
        (list "" "max(" i0 ", " i1 ")" ""))]
     ['add1
      (lambda (lws)
        (define-values (add1 i0)
          (values
           (list-ref lws 1)
           (list-ref lws 2)))
        (list "" i0 " + 1" ""))]
     ['apply
      (lambda (lws)
        `("" "(" ,@(drop lws 2) ")" ""))])
    (bla)))

(define-syntax-rule (render-term e)
  (wrap (thunk (_render-term ttL e))))

(define-syntax-rule (render-judgment-form e)
  (wrap (thunk (_render-judgment-form e))))

(define-syntax-rule (render-language e)
  (wrap (thunk (_render-language e))))

(define-syntax-rule (render-reduction-relation e ...)
  (wrap (thunk (_render-reduction-relation e ...))))
