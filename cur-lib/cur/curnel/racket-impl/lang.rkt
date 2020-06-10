#lang racket/base

(require
 racket/require-syntax
 racket/provide-syntax
 (for-syntax
  ;; imported for export
  (except-in racket import export)
  racket/syntax
  syntax/parse
  ;racket/require-transform
  racket/provide-transform
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
  [typed-data data]
  [typed-elim new-elim]
  [deprecated-typed-elim elim]
  [cur-void void]
  #;[cur-require require]
  [cur-provide provide])
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
 provide-with-types

 #%top #%top-interaction
 #%module-begin)

#;(define-syntax (cur-require syn)
  (syntax-parse syn
    [(_ specs ...)
     #'(require (require-with-type spec) ...)]))

(define-syntax (cur-provide syn)
  (syntax-parse syn
    [(_ spec ...)
     #'(provide (provide-with-types spec) ...)]))

;(define-require-syntax (require-with-type stx)
;  (syntax-case stx ()
;    [(_ spec)
;     (let-values ([(imports _) (expand-import #'spec))]
;       #`(combine-in
;          spec
;          (for-syntax
;           #,@(for/list ([i (in-list imports)])
;                (import-src-sym i))))
;       )]))

(define-provide-syntax (provide-with-types stx)
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
