#lang racket/base

(require
 racket/syntax
 (for-template
  "runtime.rkt"))

(provide
 cur-apply*
 type-of-constant
 type-of-id
 call-with-ctx
 build-dispatch)

#|
Utilities for working with cur-runtime-terms
 |#

; rator must be a cur-runtime-term?, and rands must be a list of cur-runtime-terms?
; The result is a cur-runtime-term?
(define (cur-apply* rator rands)
  (if (null? rands)
      rator
      (cur-apply* #`(#%plain-app cur-apply #,rator #,(car rands)) (cdr rands))))

; Expects an identifier defined as a Cur constant, and it's argument as cur-runtime-term?s
; Returns it's type as a cur-runtime-term?
(define (type-of-constant name args)
  ; NB: eval is evil, but this is the least bad way I can figured out to store types.
  (apply (constant-info-type-constr (syntax-local-eval name)) args))

; Expects an identifier defined as a Cur identifier
; Returns it's type as a cur-runtime-term?
(define (type-of-id name)
  (identifier-info-type (syntax-local-eval name)))

; Excepts an ordered list of pairs of an identifier and a type, as a cur-runtime-term, and a thunk.
; Adds a binding for each identifier to the identifier-info containing the type, within the scope of
; the thunk.
(define (call-with-ctx ctx th)
  (parameterize ([current-namespace (current-namespace)])
    (for ([name (map car ctx)]
          [type (map cdr ctx)])
      (namespace-set-variable-value! (syntax-e name) (identifier-info type #f) #f))
    (th)))

;; TODO PERF: Should be able to do a better job since predicates are mutually exclusive.
(define (build-dispatch predicates)
  (lambda (ls)
    (lambda (e)
      (let/ec k
        (for ([p predicates]
              [l ls]
              #:when (p e))
          (k l))
        ;; NB: This error should be impossible when used with well-typed code.
        (error 'build-dispatch "Something very very bad has happened.")))))

(module+ test
  (require
   "runtime.rkt"
   (submod "runtime.rkt" test)
   (for-syntax
    racket/base
    chk
    "alpha-equiv.rkt"
    (submod "..")))
  (begin-for-syntax
    (chk
     #:eq cur-α-equal? (type-of-id #'two) #'(#%plain-app Nat)
     #:eq cur-α-equal? (type-of-constant #'Nat '()) #'(#%plain-app cur-Type '0)
     #:eq cur-α-equal? (type-of-constant #'z '()) #'(#%plain-app Nat)
     #:eq cur-α-equal? (call-with-ctx
                        (list (cons #'x #'(#%plain-app Nat)))
                        (lambda () (type-of-id #'x))) #'(#%plain-app Nat))))
