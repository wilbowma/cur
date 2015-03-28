#lang s-exp "../redex-curnel.rkt"
(provide bool btrue bfalse if bnot)

(data bool : Type
  (btrue : bool)
  (bfalse : bool))

(define-syntax (if syn)
  (syntax-case syn ()
    [(_ t s f)
     ;; Compute the motive
     (let ([M #`(lambda (x : #,(type-infer/syn #'t))
                  #,(type-infer/syn #'s))])
       #`(elim bool t #,M s f))]))

(define (bnot (x : bool)) (if x bfalse btrue))
(module+ test
  (require rackunit)
  (check-equal? (bnot btrue) bfalse)
  (check-equal? (bnot bfalse) btrue))
