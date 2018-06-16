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
 (build-list
  Ascii
  (cur-apply ascii true true false true true false true)
  (cur-apply ascii true true false false true false true)
  (cur-apply ascii true true false true true true true)
  (cur-apply ascii true true true false true true true)))

(check-equal?
 (cur-datum . 5)
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
