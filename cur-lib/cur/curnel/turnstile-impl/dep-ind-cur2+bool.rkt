#lang s-exp "dep-ind-cur2.rkt"
(require turnstile/typedefs 
         "dep-ind-cur2+data2.rkt")

;; bool lib

(provide False True I And conj Or or_introL or_introR
         elim-Or elim-And)

;(define-type Bool : Type)

(define-type False : Type)

(define-datatype True : Type
  [I : True])

(define-datatype And [X : Type] [Y : Type] : -> Type
  [conj : [x : X] [y : Y] -> (And X Y)])

(define-datatype Or [X : Type] [Y : Type] : -> Type
  [or_introL : [x : X] -> (Or X Y)]
  [or_introR : [y : Y] -> (Or X Y)])

(module* tauto #f
  (require turnstile
           (for-syntax syntax/parse)
           (only-in "dep-ind-cur2+sugar.rkt" [#%app typed-app]))

  (provide tauto)
  
  (define-for-syntax tautology
    (syntax-parser
;      [_ #:do[(printf "tauto: ~a\n" (stx->datum this-syntax))] #:when #f #'debug]
      [~True #'I]
      [(~And X Y)
       #:when (and (tautology #'X) (tautology #'Y))
       #`(typed-app conj X Y (tauto X) (tauto Y))]
      [(~Or X Y)
       #:when (tautology #'X)
       #'(typed-app or_introL X Y (tauto X))]
      [(~Or X Y)
       #:when (tautology #'Y)
       #'(typed-app or_introR X Y (tauto Y))]
      [_ #f]))

  (define-syntax tauto
    (syntax-parser
      [(_ prop)
       #:do[(define res (tautology (expand/df #'prop)))]
       (or res (type-error #:src #'prop #:msg "no proof"))])))
