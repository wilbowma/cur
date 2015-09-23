#lang s-exp "../cur.rkt"
(require "sugar.rkt")
(provide Bool true false if not and or)

(data Bool : Type
  (true : Bool)
  (false : Bool))

(define-syntax (if syn)
  (syntax-case syn ()
    [(_ t s f)
     ;; Compute the motive
     (let ([M #`(lambda (x : #,(type-infer/syn #'t))
                  #,(type-infer/syn #'s))])
       (quasisyntax/loc syn (elim Bool t #,M s f)))]))

(define (not (x : Bool)) (if x false true))

(module+ test
  (require rackunit)
  (check-equal? (not true) false)
  (check-equal? (not false) true))
