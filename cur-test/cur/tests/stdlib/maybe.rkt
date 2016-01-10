#lang cur

(require
 rackunit
 cur/stdlib/bool
 cur/stdlib/maybe)

(check-equal?
 (some/i true)
 (some Bool true))
;; Disabled until #22 fixed
#;(check-equal?
   (case* Maybe Type (some Bool true) (Bool)
          (lambda* (A : Type) (x : (Maybe A)) A)
          [(none (A : Type)) IH: ()
           false]
          [(some (A : Type) (x : A)) IH: ()
           ;; TODO: Don't know how to use dependency yet
           (if x true false)])
   true)
