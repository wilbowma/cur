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
  [typed-data data]
  [typed-elim new-elim]
  [depricated-typed-elim elim]
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
