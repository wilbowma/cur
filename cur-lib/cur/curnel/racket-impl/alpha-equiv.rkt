#lang racket/base

(require
 syntax/parse
 "stxutils.rkt"
 (for-template
  "runtime.rkt"))

(provide cur-α-equal?)

; t1 and t2 must both be cur-runtime-terms?
(define (cur-α-equal? t1 t2 (fail (lambda _ #f)))
  (let cur-α-equal? ([t1 t1] [t2 t2])
    (syntax-parse #`(#,t1 #,t2)
      [(x:cur-runtime-identifier y:cur-runtime-identifier)
       (free-identifier=? #'x #'y)]
      [(e1:cur-runtime-constant e2:cur-runtime-constant)
       (and (cur-α-equal? #'e1.name #'e2.name)
            (andmap cur-α-equal? (attribute e1.rand-ls) (attribute e2.rand-ls)))]
      [(A:cur-runtime-universe B:cur-runtime-universe)
       (eq? (attribute A.level) (attribute B.level))]
      [(e1:cur-runtime-pi e2:cur-runtime-pi)
       (and (cur-α-equal? #'e1.ann #'e2.ann)
            (cur-α-equal? #'e1.result (subst #'e1.name #'e2.name #'e2.result)))]
      [(e1:cur-runtime-elim e2:cur-runtime-elim)
       (and (cur-α-equal? #'e1.target #'e2.target)
            (cur-α-equal? #'e1.motive #'e2.motive)
            (andmap cur-α-equal? (attribute e1.method-ls) (attribute e2.method-ls)))]
      [(e1:cur-runtime-app e2:cur-runtime-app)
       (and (cur-α-equal? #'e1.rator #'e2.rator)
            (cur-α-equal? #'e1.rand #'e2.rand))]
      [(e1:cur-runtime-lambda e2:cur-runtime-lambda)
       (and (cur-α-equal? #'e1.ann #'e2.ann)
            (cur-α-equal? #'e1.body (subst #'e1.name #'e2.name #'e2.body)))]
      [(e1:cur-runtime-term e2:cur-runtime-term)
       (fail t1 t2)])))

(module+ test
  (require
   (for-syntax
    chk
    (except-in racket/base λ)
    (submod ".."))
   "runtime.rkt"
   (submod "runtime.rkt" test))
  (begin-for-syntax
    (chk
     ; cur-α-equal? tests
     #:t (cur-α-equal? #'(#%plain-app cur-Type '0) #'(#%plain-app cur-Type '0))
     #:t (cur-α-equal? #'(#%plain-app cur-Type '1) #'(#%plain-app cur-Type '1))
     #:! #:t (cur-α-equal? #'(#%plain-app cur-Type '1) #'(#%plain-app cur-Type '0))
     #:! #:t (cur-α-equal? #'(#%plain-app cur-Type '0) #'(#%plain-app cur-Type '1))
     #:t (cur-α-equal? #'(#%plain-app Nat) #'(#%plain-app Nat))
     #:! #:t (cur-α-equal? #'(#%plain-app Nat) #'(#%plain-app z))
     #:t (cur-α-equal? #'(#%plain-app z) #'(#%plain-app z))
     #:t (cur-α-equal? #'(#%plain-app s (#%plain-app z)) #'(#%plain-app s (#%plain-app z)))
     #:t (cur-α-equal? #'(#%plain-app cur-λ (#%plain-app Nat) (#%plain-lambda (x) x))
                       #'(#%plain-app cur-λ (#%plain-app Nat) (#%plain-lambda (y) y)))
     #:t (cur-α-equal? #'(#%plain-app cur-Π (#%plain-app Nat) (#%plain-lambda (x) (#%plain-app Nat)))
                       #'(#%plain-app cur-Π (#%plain-app Nat) (#%plain-lambda (y) (#%plain-app Nat)))))))
