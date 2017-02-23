#lang racket/base

(require
 racket/syntax
 syntax/parse
 "runtime-utils.rkt"
 "stxutils.rkt"
 (for-template
  "runtime.rkt"))

(provide cur-eval)

; Expects a cur-runtime-term? and returns a cur-runtime-term?
(define (cur-eval syn)
  (let cur-eval ([syn syn])
    (syntax-parse syn
      [_:cur-runtime-universe syn]
      #;[e:cur-runtime-constant
       (make-cur-runtime-constant syn #'e.name (map cur-eval (attribute e.rand-ls)))]
      [e:cur-runtime-identifier
       #:do [(define maybe-def (identifier-def #'e.name))]
       (or (and maybe-def (cur-eval maybe-def)) syn)]
      [_:cur-runtime-identifier
       syn]
      [e:cur-runtime-pi
       (make-cur-runtime-pi syn (cur-eval #'e.ann) #'e.name (cur-eval #'e.result))]
      [e:cur-runtime-app
       #:with a (cur-eval #'e.rand)
       (syntax-parse (cur-eval #'e.rator)
         [f:cur-runtime-lambda
          (cur-eval (subst #'a #'f.name #'f.body))]
         [e1-
          (make-cur-runtime-app this-syntax #'e1- #'a)])]
      [e:cur-runtime-elim
       #:with target:cur-runtime-constant #'e.target
       #:do [(define info (syntax-local-eval #'target.name))]
       #:do [(define recursive-index-ls (constant-info-recursive-index-ls info))]
       ;; TODO PERF: use unsafe version of list operators and such for internal matters
       ;; TODO PERF: list-ref; could we make it a vector?
       (cur-eval
        (cur-apply*
         syn
         (list-ref (attribute e.method-ls) (constant-info-constructor-index info))
         (append (attribute target.rand-ls)
                 (for/fold ([m-args '()])
                           ([arg (attribute target.rand-ls)]
                            [i (in-naturals (constant-info-param-count info))]
                            ;; TODO PERF: memq in a loop over numbers...
                            #:when (memq i recursive-index-ls))
                   (cons
                    (make-cur-runtime-elim syn arg #'e.motive (attribute e.method-ls))
                    m-args)))))]
      [e:cur-runtime-elim
       (make-cur-runtime-elim syn (cur-eval #'e.target) (cur-eval #'e.motive) (map cur-eval (attribute e.method-ls)))]
      [e:cur-runtime-lambda
       (make-cur-runtime-lambda syn (cur-eval #'e.ann) #'e.name (cur-eval #'e.body))]
      [_ (raise-syntax-error 'cur-eval (format "Something has gone horribly wrong: ~a" (syntax->datum syn)) syn)])))
