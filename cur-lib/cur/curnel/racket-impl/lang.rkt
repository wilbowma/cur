#lang racket/base

(require
 racket/require-syntax
 racket/provide-syntax
 (for-syntax
  ;; imported for export
  (except-in racket import export)
  racket/syntax
  syntax/parse
  racket/require-transform
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
  [cur-require require]
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
 only-in except-in prefix-in rename-in combine-in relative-in only-meta-in for-syntax
 for-template for-label for-meta submod lib file planet

 all-defined-out all-from-out rename-out except-out prefix-out struct-out combine-out
 protect-out for-meta for-syntax for-template for-label
 provide-with-types

 #%top #%top-interaction
 #%module-begin)

(define-syntax (cur-require syn)
  (syntax-parse syn
    [(_ spec ...)
     #'(require (require-with-types spec) ...)]))

(define-syntax (cur-provide syn)
  (syntax-parse syn
    [(_ spec ...)
     #'(provide (provide-with-types spec) ...)]))

(define-syntax require-with-types
  (make-require-transformer
   (lambda (stx)
     (syntax-case stx ()
       [(_ spec)
     (let-values ([(imports src) (expand-import #'spec)])
       ;; Remove any type:id where id is not in imports.
       (define (remove-types imports)
         (for/fold ([ls '()])
                   ([i imports])
           ; if i is a type:id
           (let ([m (regexp-match #rx"type:(.*)" (symbol->string (import-src-sym i)))])
             ; and id is not in imports
             (if (and m
                      (not
                         (findf (lambda (x)
                                  (eq? (import-src-sym x)
                                       (string->symbol (second m))))
                                imports)))
                 ls
                 (cons i ls)))))

       ;; Then rename any type:id where id has been renamed
       (define (rename-types imports)
         (for/fold ([ls '()])
                   ([i imports])
           ; if i is a type:id
           (let* ([m (regexp-match #rx"type:(.*)" (symbol->string (import-src-sym i)))]
                  [id (and m (findf
                              (lambda (x)
                                (eq? (import-src-sym x) (string->symbol (second m))))
                              imports))])
             ; id can be assumed to be imported since remove-types has run.
             ; and id has been renamed
             (if (and m (not (eq? (import-src-sym id)
                                  (syntax->datum (import-local-id id)))))
                 (cons
                  (struct-copy
                   import
                   i
                   [local-id
                    (make-type-name (import-local-id id))])
                  ls)
                 (cons i ls)))))
       (values
        (rename-types (remove-types imports))
        src))]))))

;; TODO: Rewrite like above
(define-provide-syntax (provide-with-types stx)
  (syntax-case stx ()
    [(_ spec)
     (let ([exports (expand-export #'spec '())])
       #`(combine-out
          spec
          (for-syntax
           #,@(for/list ([i (in-list exports)]
                         #:when (with-handlers ([values (lambda _ #f)])
                                  (identifier-info? (syntax-local-eval (make-type-name (export-local-id i))))))
                #`(rename-out [#,(make-type-name (export-local-id i)) #,(make-type-name-sym (export-out-sym i))])))))]))
