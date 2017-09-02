#lang racket/base

(require
 racket/function
 (for-syntax
  racket/base
  syntax/parse
  racket/syntax
  "curnel/racket-impl/runtime.rkt")
 "curnel/racket-impl/runtime.rkt"
 "curnel/racket-impl/runtime-utils.rkt"

 )

(define-syntax (Type syn)
  (raise-syntax-error "Type doesn't make sense in a unityped setting" syn))

(define-syntax (Π syn)
  (raise-syntax-error "Π doesn't make sense in a unityped setting" syn))

(begin-for-syntax
  (define-syntax-class (data-args pos) #:attributes (recursive-index-ls names)
    (pattern ()
             #:attr recursive-index-ls '()
             #:attr names '())

    (pattern (name:id . (~var rest (data-args (add1 pos))))
             #:attr names (cons #'name (attribute rest.names))
             #:attr recursive-index-ls (attribute rest.recursive-index-ls))

    (pattern (name:id #:recursive . (~var rest (data-args (add1 pos))))
             #:attr names (cons #'name (attribute rest.names))
             #:attr recursive-index-ls (cons #`#,pos (attribute rest.recursive-index-ls)))))

(define-syntax (data syn)
  (syntax-parse syn
    [(_ name (c . (~var a (data-args 1))) ...)
     #:with dispatch (format-id this-syntax "~a-dispatch" #'name #:source #'name)
     #:with structD (format-id #'name "constant:~a" #'name #:source #'name)
     #:with (structC ...) (map (lambda (x) (format-id x "constant:~a" x #:source x)) (attribute c))
     #:with (c-name-pred ...) (map (lambda (x) (format-id x "constant:~a?" x #:source x)) (attribute c))
     #:with ((names ...) ...) (attribute a.names)
     #:with ((recursive-index-ls ...) ...) (attribute a.recursive-index-ls)
     #`(begin
         (define dispatch (box #f))
         (struct structD constant () #:transparent
           #:reflection-name 'name
           #:property prop:parameter-count '0)
         (define name ((curry structD)))

         (struct structC constant (names ...) #:transparent
           #:reflection-name 'c
           #:property prop:parameter-count '0
           #:property prop:dispatch dispatch
           #:property prop:recursive-index-ls (list recursive-index-ls ...))
         ...

         (define c ((curry structC))) ...

         (set-box! dispatch (build-dispatch (list c-name-pred ...))))]))

(define-syntax (λ syn)
  (syntax-parse syn
    [(_ (x) e)
     (make-cur-runtime-lambda syn #f #'x #'e)]))

(define-syntax (app syn)
  (syntax-parse syn
    [(_ e1 e2)
     (make-cur-runtime-app syn #'e1 #'e2)]))

(define-syntax (elim syn)
  (syntax-parse syn
    [(_ target e ...)
     (make-cur-runtime-elim syn #'target #f (attribute e))]))

(module+ test

  (data Nat (z) (s n #:recursive))
  z
  s
  (s z)

  (app (λ (x) x) (s z))

  (elim z z (λ (x) x))
  (elim (s z) z (λ (x) x))
  (elim (s (s z)) z (λ (x) x))
  )
