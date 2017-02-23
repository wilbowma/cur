#lang racket/base

(require
 racket/syntax
 syntax/parse
 racket/list
 "stxutils.rkt"
 (for-template
  "runtime.rkt"))

(provide
 cur-apply*
 make-cur-runtime-lambda*
; type-of-constant
 type-of-id
 identifier-def
 call-with-ctx
 build-dispatch

 cur-runtime-constant
 make-cur-runtime-constant
 cur-runtime-telescope
 cur-runtime-axiom-telescope
 cur-runtime-inductive-telescope
 cur-runtime-constructor-telescope

 cur-runtime-constant?
 cur-runtime-axiom-telescope?

 )

#|
Utilities for working with cur-runtime-terms
 |#

; rator must be a cur-runtime-term?, and rands must be a list of cur-runtime-terms?
; The result is a cur-runtime-term?
(define (cur-apply* syn rator rands)
  (if (null? rands)
      rator
      (cur-apply* syn (make-cur-runtime-app syn rator (car rands)) (cdr rands))))

(define (make-cur-runtime-lambda* syn name-ls ann-ls body)
  (for/fold ([result body])
            ;; TODO PERF: By using vectors, could efficiently iterate in reverse. That applies to other
            ;; uses of -ls
            ([name (reverse name-ls)]
             [ann (reverse ann-ls)])
    (make-cur-runtime-lambda syn ann name result)))

;; TODO: For future use
; Expects an identifier defined as a Cur constant, and it's argument as cur-runtime-term?s
; Returns it's type as a cur-runtime-term?
#;(define (type-of-constant name args)
  ; NB: eval is evil, but this is the least bad way I can figured out to store types.
  (apply (constant-info-type-constr (syntax-local-eval name)) args))

(require syntax/id-table racket/dict)
(define gamma (make-parameter (make-immutable-free-id-table #:phase -1)))

; Expects an identifier defined as a Cur identifier
; Returns it's type as a cur-runtime-term?
(define (type-of-id name)
  (identifier-info-type (dict-ref (gamma) name (lambda () (syntax-local-eval name)))))

(define (identifier-def name)
  ;; TODO: Catch specific error
  (with-handlers ([values (lambda (_) #f)])
    (identifier-info-delta-def (syntax-local-eval name))))

; Excepts an ordered list of pairs of an identifier and a type, as a cur-runtime-term, and a thunk.
; Adds a binding for each identifier to the identifier-info containing the type, within the scope of
; the thunk.
(define (call-with-ctx ctx th)
  (parameterize ([gamma (for/fold ([g (gamma)])
                                  ([name (map car ctx)]
                                   [type (map cdr ctx)])
                          (dict-set g name (identifier-info type #f)))])
    (th)))
#;(define (call-with-ctx ctx th)
  (define name-ls (map car ctx))
  (for ([name name-ls]
        [type (map cdr ctx)])
    (namespace-set-variable-value! (syntax-e name) (identifier-info type #f) #f ns))
  (let ([r (th)])
    ;; NB: Can't make a copy of of the current namespace, so need to manually clean up.
    (for ([name name-ls])
      ;; TODO: Catch or detect the specific error;
      ;; NB: when dealing with lexical variables, it is normal
      ;; that a shadowed variable gets undefined multiple tmies.
      (with-handlers ([(lambda (_) #t) (lambda (_) (void))])
        (namespace-undefine-variable! (syntax-e name) ns)))
    r))

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

;;; Composite runtime forms

;; Constants are nested applications with a constructor or inductive type in head position:
;; refieid-constant ::= Θ[c]
;; Θ ::= hole (Θ e)

;; NB: Used to prevent append in a loop
(define-syntax-class _runtime-constant #:attributes (name reversed-rand-ls constructor-index)
  (pattern app:cur-runtime-app
           #:with e:_runtime-constant #'app.rator
           #:attr reversed-rand-ls (cons #'app.rand (attribute e.reversed-rand-ls))
           #:attr name #'e.name
           #:attr constructor-index (attribute e.constructor-index))

  (pattern name:id
           ;; TODO: maybe should have a constant-info attr
           ;; TODO: catch proper error
           ;; TODO: Abstract this syntax-local-eval madness
           #:when (constant-info? (with-handlers ([values (lambda (_) #f)])
                                    (syntax-local-eval #'name)))
           #:attr reversed-rand-ls '()
           #:attr constructor-index (constant-info-constructor-index (syntax-local-eval #'name))))

(define-syntax-class/pred cur-runtime-constant #:attributes (name rand-ls constructor-index index-rand-ls)
  (pattern e:_runtime-constant
           #:attr name #'e.name
           #:attr rand-ls (reverse (attribute e.reversed-rand-ls))
           #:attr index-rand-ls (drop (attribute rand-ls) (constant-info-param-count (syntax-local-eval #'name)))
           #:attr constructor-index (attribute e.constructor-index)))

(define make-cur-runtime-constant cur-apply*)

;; Telescopes are nested Π types.
(define-syntax-class cur-runtime-telescope #:attributes (length name-ls ann-ls result)
  (pattern e:cur-runtime-pi
           #:with tmp:cur-runtime-telescope #'e.result
           #:attr result #'tmp.result
           #:attr length (add1 (attribute tmp.length))
           #:attr name-ls (cons #'e.name (attribute tmp.name-ls))
           #:attr ann-ls (cons #'e.ann (attribute tmp.ann-ls)))

  (pattern (~and result (~not _:cur-runtime-pi))
           #:attr length 0
           #:attr name-ls '()
           #:attr ann-ls '()))

;; Axiom telescopes are nested Π types with a universe or constant as the final result
(define-syntax-class/pred cur-runtime-axiom-telescope #:attributes (length name-ls ann-ls result)
  (pattern e:cur-runtime-telescope
           #:with (~and result (~or _:cur-runtime-universe _:cur-runtime-constant)) #'e.result
           #:attr length (attribute e.length)
           #:attr name-ls (attribute e.name-ls)
           #:attr ann-ls (attribute e.ann-ls)))

;; Inductive telescopes are nested Π types with a universe as the final result.
(define-syntax-class cur-runtime-inductive-telescope #:attributes (length name-ls ann-ls result)
  (pattern e:cur-runtime-telescope
           #:with result:cur-runtime-universe #'e.result
           #:attr length (attribute e.length)
           #:attr name-ls (attribute e.name-ls)
           #:attr ann-ls (attribute e.ann-ls)))

;; Constructor telescopes are nested Π types that return a constant with the inductive type type in
;; head position.
(define-syntax-class (cur-runtime-constructor-telescope inductive)
  #:attributes (length name-ls ann-ls recursive-index-ls result)
  (pattern e:cur-runtime-telescope
           #:with result:cur-runtime-constant #'e.result
           #:when (free-identifier=? #'result.name inductive)
           #:attr length (attribute e.length)
           #:attr name-ls (attribute e.name-ls)
           #:attr ann-ls (attribute e.ann-ls)
           ;; TODO: Is this necessary since we have constant-info now?
           #:attr recursive-index-ls
           (for/list ([t (attribute ann-ls)]
                      [i (attribute length)]
                      #:when (syntax-parse t
                               [e:cur-runtime-constant
                                (free-identifier=? #'e.name inductive)]
                               [_ #f]))
             ;; NB: Would like to return x, but can't rely on names due to alpha-conversion
             i)))
