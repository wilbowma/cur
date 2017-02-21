#lang racket/base

(require
 (for-syntax
  ;; imported for export
  racket
  racket/syntax
  syntax/parse
  "stxutils.rkt"
  "runtime-utils.rkt"

  "reflection.rkt")
 "runtime.rkt"
 "type-check.rkt")
(provide
 (rename-out
  [typed-Type Type]
  [typed-define define]
  [typed-λ λ]
  [typed-Π Π]
  [typed-app #%app]
  [typed-axiom axiom]
  [typed-data new-data]
  [depricated-cur-data data]
  [typed-elim new-elim]
  [depricated-cur-elim elim]
  [cur-void void])
 begin
 ;; TODO: Don't export these by default; export in library or so
;; DYI syntax extension
  define-syntax
  begin-for-syntax
  define-for-syntax
  syntax-case
  syntax-rules
  define-syntax-rule
  (for-syntax
   (all-from-out syntax/parse)
   (all-from-out racket)
   (all-from-out racket/syntax)
   (all-from-out "reflection.rkt"))
 require only-in except-in prefix-in rename-in combine-in relative-in only-meta-in for-syntax
 for-template for-label for-meta submod lib file planet

 provide all-defined-out all-from-out rename-out except-out prefix-out struct-out combine-out
 protect-out for-meta for-syntax for-template for-label

 #%top #%top-interaction
 #%module-begin)

;; Backward compatible elimination syntax
(define-syntax (depricated-cur-elim syn)
  (syntax-case syn ()
    [(_ _ motive (methods ...) target)
     (quasisyntax/loc syn (typed-elim target motive methods ...))]))

(define-syntax-rule (cur-void)
  (#%plain-app void))

;; backward compatible data
(require (for-template "runtime.rkt"))
(define-for-syntax (make-cur-runtime-lambda* syn name-ls ann-ls body)
  (for/fold ([result body])
            ;; TODO PERF: By using vectors, could efficiently iterate in reverse. That applies to other
            ;; uses of -ls
            ([name (reverse name-ls)]
             [ann (reverse ann-ls)])
    (make-cur-runtime-lambda syn ann name result)))

(begin-for-syntax
  ;; TODO: Copy/pasta from sugar.rkt. These depricated forms need to move there eventually.
  (define-syntax-class telescope
    #:literals (typed-Π)
    (pattern (typed-Π (x:id (~datum :) t:expr) e:telescope)
             #:attr result #'e.result
             #:attr decls (cons #'(x : t) (attribute e.decls))
             #:attr names (cons #'x (attribute e.names))
             #:attr types (cons #'t (attribute e.types)))

    (pattern (~and result:expr (~not (typed-Π _ _)))
             #:attr decls '()
             #:attr names '()
             #:attr types '())))

(define-for-syntax (eta name syn)
  (syntax-parse syn
    [e:telescope
     (make-cur-runtime-lambda*
      name
      (attribute e.names)
      (attribute e.types)
      (cur-apply* name name (attribute e.names)))]))

(require (for-syntax syntax/transformer))
(define-syntax (depricated-cur-data syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:top-level-id name:id : p:nat type:telescope (c-name:id : c-type:telescope)
                     ...)
     #:with name^ (fresh #'name)
     #:with (c-name^ ...) (map fresh (attribute c-name))
     #:with name-eta (eta #'name^ #'type)
     #:with (c-name-eta ...) (map eta (attribute c-name^) (attribute c-type))
     #:with ((c-decl ...) ...) (attribute c-type.decls)
     #`(begin
         #,(cur-elab/ctx
            #`(let-syntax ([name (make-variable-like-transformer #'name^)]
                           [c-name (make-variable-like-transformer #'c-name^)] ...)
                (typed-data (name^ #,@(attribute type.decls)) : p type.result
                            ((c-name^ c-decl ...) : c-type.result)
                            ...))
            (cons (cons #'name #'type)
                  (map cons (attribute c-name) (attribute c-type))))
         (typed-define name name-eta)
         (typed-define c-name c-name-eta) ...
         )]))
