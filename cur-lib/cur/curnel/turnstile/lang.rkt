#lang racket/base

(require
 racket/require-syntax
 racket/provide-syntax
 (for-syntax
  ;; imported for export
  (except-in racket import export)
  racket/syntax
  syntax/parse

  "stxutils.rkt"
  "runtime-utils.rkt"

  "reflection.rkt")
 ;;"runtime.rkt"
 ;;"type-check.rkt"
 "cur-to-turnstile.rkt")

(provide
 (rename-out
  [cur-Type Type]
  [cur-define define]
  [cur-λ λ]
  [cur-Π Π]
  [cur-app #%app]
  [cur-axiom axiom]
  [cur-data data]
  [cur-new-elim new-elim]
  [deprecated-cur-elim elim]
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
  require
 only-in except-in prefix-in rename-in combine-in relative-in only-meta-in for-syntax
 for-template for-label for-meta submod lib file planet

 all-defined-out all-from-out rename-out except-out prefix-out struct-out combine-out
 protect-out for-meta for-syntax for-template for-label
 provide

 #%top #%top-interaction
 #%module-begin)


; TODO: Copy pasted from racket lang
#;(define-syntax (cur-provide syn)
  (syntax-parse syn
    [(_ spec ...)
     #'(provide spec ...)]))

#;(define-provide-syntax (provide-with-types stx)
  (syntax-case stx ()
    [(_ spec)
     (let ([exports (expand-export #'spec '())])
       #`(combine-out
          spec
          (for-syntax
           #,@(for/list ([i (in-list exports)]
                         #:when (with-handlers ([values (lambda _ #f)])
                                  (identifier-info? (syntax-local-eval (export-local-id i)))))
                #`(rename-out [#,(export-local-id i) #,(export-out-sym i)])))))]))

(define-syntax (deprecated-cur-elim syn)
  (syntax-case syn ()
    [(_ _ motive (methods ...) target)
     (quasisyntax/loc syn (cur-new-elim target motive (methods ...)))]))
