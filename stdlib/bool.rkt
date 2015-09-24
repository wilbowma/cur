#lang s-exp "../redex-curnel.rkt"
(provide bool btrue bfalse if bnot)

(data bool : Type
  (btrue : bool)
  (bfalse : bool))

(define-syntax (if syn)
  (syntax-case syn ()
    [(_ t s f)
     ;; Compute the motive
     (let* ([sty (type-infer/syn #'s)]
            [M #`(lambda (x : #,(type-infer/syn #'t))
                  #,sty)]
            [U (type-infer/syn sty)])
       (quasisyntax/loc syn (elim bool #,U #,M s f t)))]))

(define (bnot (x : bool)) (if x bfalse btrue))
(module+ test
  (require rackunit)
  (check-equal? (bnot btrue) bfalse)
  (check-equal? (bnot bfalse) btrue))
