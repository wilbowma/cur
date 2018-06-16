#lang racket/base

(require
 (only-in cur/stdlib/sugar [#%app cur-apply])
 (only-in cur/stdlib/datum [#%datum cur-datum])
 (except-in cur/stdlib/ascii #%datum)
 (except-in cur/stdlib/nat #%datum)
 cur/stdlib/bool
 cur/stdlib/list)

(require rackunit)
;; TODO: Need expression-level language boundary.
;; Racket only provides module-level
(check-equal?
 (cur-datum . "meow")
 ;; build-list is a macro, so no need for cur-apply
 (build-list
  Ascii
  (cur-apply ascii true true false true true false true)
  (cur-apply ascii true true false false true false true)
  (cur-apply ascii true true false true true true true)
  (cur-apply ascii true true true false true true true)))

(check-equal?
 (cur-datum . 5)
 ;; Can get away without cur-apply or cur-datum here, because s is secretly a macro
 (s (s (s (s (s z))))))

(check-equal?
 (cur-apply add1 (cur-datum . 5))
 (s (s (s (s (s (s z)))))))

; Syntax error
; (cur-apply add1 (cur-datum . ""))

;; TODO: I've defined data conversion procedures, e.g. meta-bool->bool,
;; nat->unary, but over syntax objects.
;; Would need to redefine them for runtime interop...
;; That's bad; need to be able to define only once
;; TODO: All meta-procedures are provided for-syntax, which makes it annoying to
;; try to require them for-meta 0. But, they are tied to syntax objects.. hm.

(displayln (s (s (s (s (s (s z)))))))

;; Let's violate type safety and manually making "" a Nat
(define x "")

(require (for-syntax (only-in racket/base #%app syntax define quote-syntax)))
(require (except-in cur/curnel/racket-impl/runtime cur-apply))
(begin-for-syntax
  (define x (identifier-info #'Nat #'"")))

(cur-apply add1 x)
