#lang racket/base

(require
 racket/function
 racket/list
 scribble/base
 (rename-in
  retex
  [render-mathpar-judgment _render-mathpar-judgment])
 typeset-rewriter
 (except-in cur/curnel/model/core apply)
 redex/reduction-semantics
 [except-in
  redex/pict
  render-term
  render-language
  render-judgment-form
  render-reduction-relation]
 pict)

(provide
 (all-defined-out)
 #;(except-out
  (all-from-out redex/pict)
  render-term)
 table-reduction-style
 (all-from-out
  cur/curnel/model/core
  pict))

(default-font-size 9)
(metafunction-font-size 9)
(label-font-size 9)
(greek-style 'roman)
(upgreek-style 'roman)
(metafunction-style 'swiss)
(label-style 'swiss)
(default-style 'roman)
(literal-style 'roman)
(paren-style 'roman)
(grammar-style 'roman)

(mathpar-judgment-negspace "-1em")

(current-render-pict-adjust
 (λ (x sym) x))

(non-terminal-subscript-style
 (cons 'large-script (non-terminal-subscript-style)))

(define-rw-context with-curnel-rws
  #:compound
  (['type-infer type-infer-rw]
   ['type-infer-normal
    (rw-lambda
     [`(type-infer-normal ,Δ ,Γ ,e ,t) =>
      `("" ,Δ ";" ,Γ " ⊢ " ,e " ⇒ " ,t "")])]
   ['type-check
    (rw-lambda
     [`(type-check ,Δ ,Γ ,e ,t) =>
      `("" ,Δ ";" ,Γ " ⊢ " ,e " ⇐ " ,t "")])]
   ['wf wf-rw]
   ['valid valid-rw]
   ['substitute substitute-rw]
   ['subtype
    (rw-lambda
     [`(subtype ,Δ ,Γ ,t1 ,t2) =>
      `("" ,Δ ";" ,Γ " ⊢ " ,t1 " ≼ " ,t2 "")])]
   ['convert
    (rw-lambda
     [`(convert ,Δ ,Γ ,t1 ,t2)
      => (list "" Δ ";" Γ " ⊢ " t1 " ≡ " t2 "")])]
   ;; NB: Manually compiled because rw-lambda was producing garbage
   ['λ
    (rw-lambda
     [`(λ (,x : ,t) ,e) =>
      `("" ,(struct-copy lw x [e "λ"] [column (- (lw-column x) 3)]) "" ,x ":" ,t "." ,e "")])]
   ['Π
    (rw-lambda
     [`(Π (,x : ,t) ,e) =>
      `(""
        ,(just-before (text "Π" (upgreek-style) (default-font-size)) x)
        ""
        ,x ":"
        ,t "." ,e
        "")])]
   ['elim
       (rw-lambda
        [`(elim ,D ,motive ,methods ,e) =>
         `(""
           ,(struct-copy lw D [e "elim"] [column (sub1 (lw-column D))])
           ""
           ,(just-before
             (text (format "~a" (lw-e D)) (non-terminal-subscript-style) (default-font-size))
             motive)
           " "
           ,motive
           ,methods
           ,e
           "")])]
   ['Γ
    (rw-lambda
     [`(Γ ,x : ,t) =>
      `(""
        ,(just-before (text "Γ" (upgreek-style) (default-font-size)) x)
        ","
        ,x
        ":"
        ,t
        "")])]
   ['∅
    (rw-lambda
     [`(∅ (,D : ,t (,b (... ...)))) =>
      `(""
        ,(just-before (text "∅" (upgreek-style) (default-font-size)) D)
        ","
        ,D
        ":"
        ,t
        " := "
        ,@b
        "")])]
   ['Δ
    (rw-lambda
     [`(Δ (,D : ,t (,b (... ...)))) =>
      `(""
        ,(just-before (text "Δ" (upgreek-style) (default-font-size)) D)
        ","
        ,D
        ":"
        ,t
        " := "
        ,@b
        "")])]
   ['Unv
    (rw-lambda
     [`(Unv ,i) =>
      `(""
        "Unv "
        ,i
;        ,(just-before (text "Unv" (literal-style) (default-font-size)) i)
;        ,(text (format "~a" (lw-e i)) (non-terminal-subscript-style) (default-font-size))
        "")])]
   ['Δ-type-in
    (rw-lambda
     [`(Δ-type-in ,Δ ,D ,t)
      => (list ""
               (set-column D values Δ) " : "
               (set-column t (curry + (lw-column-span D)) D) " ∈ "
               (set-column Δ (curry + (lw-column-span D) (lw-column-span t) -1) t)
               "")])]
   ['Δ-constr-in
    (rw-lambda
     [`(Δ-constr-in ,Δ ,c ,t)
      => (list ""
               (set-column c values Δ) " : "
               (set-column t (curry + (lw-column-span c)) c) " ∈ "
               (set-column Δ (curry + (lw-column-span c) (lw-column-span t) -1) t)
               "")])]
   ['Γ-in
    (rw-lambda
     [`(Γ-in ,Γ ,x ,t)
      =>
      (list ""
            (set-column x values Γ) " : "
            (set-column t (curry + (lw-column-span x)) x) " ∈ "
            (set-column Γ (curry + (lw-column-span x) (lw-column-span t) -1) t)
            "")])]
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
      (define-values (i0)
        (values
         (list-ref lws 2)))
      (list "" i0 " + 1" ""))]
   ['apply
    (lambda (lws)
      `("" "(" ,@(drop lws 2) ")" ""))]))

(define (curnel-format e)
  (with-curnel-rws (e)))

(define-syntax-rule (with-curnel e ...)
  (curnel-format (thunk e ...)))

(define-syntax-rule (render-term e)
  (with-curnel (render-term-cache ttL e)))

(define-syntax-rule (render-term/pretty e)
  (with-curnel (render-term/pretty-write ttL (term e))))

(define-syntax-rule (render-judgment-form e)
  (with-curnel (render-judgment-form-cache e)))

(define-syntax-rule (render-language e)
  (with-curnel (render-language-cache e)))

(define-syntax-rule (render-reduction-relation e ...)
  (with-curnel (render-reduction-relation-cache e ...)))

(define-syntax-rule (render-mathpar-judgment e ...)
  (with-curnel (_render-mathpar-judgment e ...)))
