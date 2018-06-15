#lang cur
(require
 cur/stdlib/datum
 rackunit)

(begin-for-syntax
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
