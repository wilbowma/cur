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
  
  "reflection.rkt"
 )
 ;;"runtime.rkt"
 ;;"type-check.rkt"
 "cur-to-turnstile.rkt"
 )
(provide
; (rename-out
;  [turn-Type Type]
;  [turn-define define]
;  [turn-λ λ]
;  [turn-Π Π]
;  [turn-app #%app]
;  [turn-axiom axiom]
;  [turn-data data]
;  [turn-new-elim new-elim]
;  [turn-elim elim]
;  [turn-void void]
  #;[cur-require require]
;  [turn-provide provide]
;  )
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

