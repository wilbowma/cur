#lang cur

;; issue #121, from @dmelcer9

(require cur/stdlib/list
         cur/stdlib/bool
         cur/stdlib/prop
         cur/stdlib/sugar
         cur/stdlib/sigma
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         "rackunit-ntac.rkt")

;; ok
#;(ntac/trace
   (∀
    (Σ (lst : (List Bool)) (And (== (List Bool) lst (nil Bool)) (Not (== (List Bool) lst (nil Bool)))))
    False)
   (by-intros ex)
   (by-destruct ex #:as [(aa bb)]))

;; fails before issue#121 fix
(define-theorem f
  (∀
   (T : Type)
   (Σ (lst : (List T))
      (And (== (List T) lst (nil T))
           (Not (== (List T) lst (nil T)))))
   False)
  (by-intro S)
  (by-intro ex)
  (by-destruct ex #:as [(aa bb)])
  (by-destruct bb #:as [(p pf)])
  (by-apply pf #:in p)
  by-assumption)

(:: f
    (∀ (T : Type)
       (Σ (lst : (List T))
          (And (== (List T) lst (nil T))
               (Not (== (List T) lst (nil T)))))
       False))

;; should work
;; (define core
;;   (ntac
;;    (∀ (T : Type)
;;       (x : T)
;;       (y : T)
;;       (And (== T x y) (Not (== T x y)))
;;       False)
;;    (by-intros T x y p)
;;    (by-destruct p #:as [(p pf)])
;;    (by-apply pf #:in p)
;;    by-assumption))

;; (define val (λ (T : Type)
;;               (Ex : (Σ (lst : (List T)) (And (== (List T) lst (nil T)) (Not (== (List T) lst (nil T))))))
;;               (core (List T) (fst Ex) (nil T) (snd Ex))))

;; (define verify-expected-type
;;   (ntac
;;    (∀
;;     (T : Type)
;;     (Σ (lst : (List T)) (And (== (List T) lst (nil T)) (Not (== (List T) lst (nil T)))))
;;     False)
;;    (by-exact val)))
