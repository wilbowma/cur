#lang cur
(require
 cur/stdlib/datum
 cur/stdlib/bool ; as a concrete type/value
 rackunit/turnstile+)

(typecheck-fail "" #:with-msg "Could not find datum parser")
(typecheck-fail 0 #:with-msg "Could not find datum parser")

(begin-for-syntax
  (current-datum (lambda (syn f)
                   (syntax-parse syn
                     [e:nat #'false]
                     [_ (f syn)]))))

(check-type 0 : Bool -> false)

(begin-for-syntax
  (current-datum (lambda (syn f)
                   (syntax-parse syn
                     [e:str #'true]
                     [_ (f syn)]))))

(check-type 0 : Bool -> false)
(check-type "" : Bool -> true)

#;(begin-for-syntax
  (require rackunit)
  (check-exn exn:fail? (lambda () (cur-expand #'"")))
  (check-exn exn:fail? (lambda () (cur-expand #'0)))
  (current-datum (lambda (syn f)
                   (syntax-parse syn
                     [e:nat
                      #'okay]
                     [_ (f syn)])))
  (check-equal? 'okay (syntax->datum (cur-expand #'0)))
  (current-datum (lambda (syn f)
                   (syntax-parse syn
                     [e:str
                      #'okay]
                     [_ (f syn)])))
  (check-equal? 'okay (syntax->datum (cur-expand #'0)))
  (check-equal? 'okay (syntax->datum (cur-expand #'""))))
