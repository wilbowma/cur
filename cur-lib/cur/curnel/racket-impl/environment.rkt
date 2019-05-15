#lang racket/base
(require
 racket/syntax
 syntax/id-table
 racket/dict
 (for-template
  "runtime.rkt")
 "runtime-utils.rkt")

(provide
 type-of-id
 ; type-of-constant
 identifier-def
 call-with-ctx
 bind-ctx-in)

#|
An explicit typing environment for Cur.
We try hard to reuse Racket's environment, but the reflection API seems to make
this impossible in general.
|#

;; TODO: For future use
; Expects an identifier defined as a Cur constant, and it's argument as cur-runtime-term?s
; Returns it's type as a cur-runtime-term?
#;(define (type-of-constant name args)
  ; NB: eval is evil, but this is the least bad way I can figured out to store types.
  (apply (constant-info-type-constr (syntax-local-eval name)) args))

;; TODO: Why is this a parameter instead of a syntax parameter? Well, it works, so...
(define current-cur-environment (make-parameter (make-immutable-free-id-table #:phase -1)))

; Expects an identifier defined as a Cur identifier
; Returns it's type as a cur-runtime-term?
(define (type-of-id name)
  (identifier-info-type (dict-ref (current-cur-environment) (make-type-name name) (lambda () (syntax-local-eval (make-type-name name))))))

(define (identifier-def name)
  ;; TODO: Catch specific error
  (with-handlers ([values (lambda (_) #f)])
    (identifier-info-delta-def (syntax-local-eval (make-type-name name)))))

; Excepts an ordered list of pairs of an identifier and a type, as a cur-runtime-term, and a thunk.
; Adds a binding for each identifier to the identifier-info containing the type, within the scope of
; the thunk.
(define (call-with-ctx ctx th)
  (parameterize ([current-cur-environment
                  (for/fold ([g (current-cur-environment)])
                            ([name (map car ctx)]
                             [type (map cdr ctx)])
                    (dict-set g (make-type-name name) (identifier-info type #f)))])
    (th)))

;; Binds the names of ctx in an internal definition context before calling f
;; with that internal definition context and removes the new scopes
;; afterwards.
;; This does not replace call-with-ctx, which setup up the typing environment
;; and not the syntax bindings needed during macro expansion.
;; Calling this when unnecessary can really mess up internal definition contexts.
;; TODO: Make more resilient by tracking the current internal definition context manually?
(define (bind-ctx-in ctx f)
  (define intdef (syntax-local-make-definition-context))
  (syntax-local-bind-syntaxes (map car ctx) #f intdef)
  (internal-definition-context-introduce intdef (f intdef) 'remove))

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
