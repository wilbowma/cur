#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/prop.rkt"
 "base.rkt"
 "standard.rkt")

(provide (for-syntax reflexivity))

;; `reflexivity` is defined here instead of standard.rkt
;; because it requires cur/stdlib/prop
(define-for-syntax (reflexivity ptz)
  (match-define (ntt-hole _ goal) (nttz-focus ptz))
  (ntac-match goal
   ;; TODO: use pattern expanders to abstract away these #%app's?
   [(_ (_ (_ (~literal ==) ty) a) b)
    ((fill (exact #'(refl ty a))) ptz)]))
