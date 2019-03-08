#lang racket/base
(provide define-axiom print-assumptions
         (for-syntax axiom find-all-axioms))

(require syntax/parse/define
         turnstile/base turnstile/typedefs
         (for-syntax racket/base (only-in racket/list append-map)))

;; runtime support for axioms

(define ((im-an-axiom name) . _)
  (error name "encountered axiom during evaluation"))

;; -----------
;; define-axiom
;; -----------

(define-syntax-parser define-axiom
  [(_ name:id τ)
   #'(define-syntax name
       (make-variable-like-transformer
        (assign-type #'(#%plain-app im-an-axiom 'name)
                     #'τ)))])

;; -----------
;; print-assumptions
;; -----------

(begin-for-syntax
  (define-syntax-class axiom
    #:attributes (name)
    [pattern ({~literal #%plain-app}
              {~literal im-an-axiom}
              ({~literal quote} name:id))])

  ;; syntax -> [hash symbol => type]
  (define (find-all-axioms stx)
    (let find ([axioms (hasheq)]
               [stx stx])
      (syntax-parse stx
        [a:axiom
         (hash-update axioms
                      (syntax-e #'a.name)
                      values
                      (λ ()
                        (resugar-type (typeof stx))))]
        [(stuff ...)
         (for/fold ([ax axioms]) ([stx (in-list (attribute stuff))])
           (find ax stx))]
        [_ axioms]))))

(define-syntax-parser print-assumptions
  [(_ expr)
   #:with [(axiom-name . axiom-type) ...]
          (hash->list (find-all-axioms (expand/df #'expr)))
   #'(begin
       (printf "Axioms used by \"~s\":\n" 'expr)
       (printf " - ~s : ~s\n" 'axiom-name 'axiom-type)
       ...)])
