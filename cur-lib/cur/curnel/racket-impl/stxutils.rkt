#lang racket/base
(require
 (for-syntax
  racket/base
  syntax/parse
  racket/syntax)
 (for-template (only-in racket/base let-values #%plain-lambda))
 syntax/parse
 racket/syntax
 syntax/stx
 syntax/parse/experimental/reflect)

(provide (all-defined-out))

(define (local-expand-expr x) (local-expand x 'expression null))

(define (reified-syntax-class->pred stxclass)
  (lambda (expr)
    (syntax-parse expr
      [(~reflect _ (stxclass)) #t]
      [_ #f])))

(define-syntax-rule (syntax-class->pred id)
  (reified-syntax-class->pred (reify-syntax-class id)))

(define-syntax (define-syntax-class/pred stx)
  (syntax-parse stx
    [(_ name:id expr ...)
     #:with pred? (format-id #'name "~a?" #'name)
     #`(begin
         (define-syntax-class name expr ...)
         (define pred? (syntax-class->pred name)))]))

(require syntax/id-set)
(define (subst v x syn [bvs (immutable-free-id-set)])
  (syntax-parse syn
    [y:id
     #:when (and (free-identifier=? syn x)
                 (not (free-id-set-member? bvs x)))
     v]
    ; something wrong with hygiene, so need this explicit case
    ; o.w., λ binders get substed
    [((~and (~literal #%plain-lambda) lam) (z:id) e)
     #`(lam (z) #,(subst v x #'e (free-id-set-add bvs #'z)))]
    [(e ...)
     (datum->syntax syn (map (lambda (e) (subst v x e bvs)) (attribute e)))]
    [_ syn]))

(define (stx=? e1 e2)
  ;; (printf "(stx=) e1 = ~a\n" e1)
  ;; (printf "(stx=) e2 = ~a\n" e2)
  (define res
    (or (and (identifier? e1) (identifier? e2)
             (free-identifier=? e1 e2))
        (and (number? (syntax-e e1)) (number? (syntax-e e2))
             (= (syntax-e e1) (syntax-e e2))) ; number literals
        (and (stx-pair? e1) (stx-pair? e2)
             (= (length (syntax->list e1)) (length (syntax->list e2)))
             (andmap stx=? (syntax->list e1) (syntax->list e2)))))
;;  (displayln res)
  res)

(define (subst-term v e0 syn [bvs (immutable-free-id-set)])
; (printf "subst-term: ~a for ~a in ~a\n" (syntax->datum v) (syntax->datum e0) (syntax->datum syn))
  (syntax-parse syn
    [e
     #:when (and (stx=? #'e e0)
                 (or (not (identifier? #'e))
                     (not (free-id-set-member? bvs #'e))))
     v]
    [((~and (~datum λ) lam) (z:id : ty) e)
     #`(lam (z : #,(subst-term v e0 #'ty bvs)) #,(subst-term v e0 #'e (free-id-set-add bvs #'z)))]
    [(e ...)
     (datum->syntax syn (map (λ (e1) (subst-term v e0 e1 bvs)) (attribute e)))]
    [_ syn]))

;; takes a list of values and a list of identifiers, in dependency order, and substitutes them into syn.
;; TODO PERF: reverse
(define (subst* v-ls x-ls syn)
  (for/fold ([syn syn])
            ([v (reverse v-ls)]
             [x (reverse x-ls)])
    (subst v x syn)))

(define-syntax-class top-level-id #:attributes ()
  #:commit
  (pattern x:id
           #:fail-unless (case (syntax-local-context)
                           [(module top-level module-begin) #t]
                           [else #f])
           (raise-syntax-error
            (syntax->datum #'x)
            (format "Can only use ~a at the top-level."
                    (syntax->datum #'x))
            this-syntax)))

(define-syntax-class definition-id #:attributes ()
  #:commit
  (pattern x:id
           #:fail-unless (not (eq? (syntax-local-context) 'expression))
           (raise-syntax-error
            (syntax->datum #'x)
            (format "Can only use ~a in definition context."
                    (syntax->datum #'x))
            this-syntax)))

(define-syntax-class in-let-values #:attributes (body)
  #:literals (let-values)
  #:commit
  (pattern (let-values _ e:in-let-values)
           #:attr body #'e.body)
  (pattern body:expr))

;; Try to make readable fresh names.
  (define fresh
    (let ([n 0])
      (lambda ([x #f])
        (set! n (add1 n))
        (format-id x "~a~a" (or x 'x) n #:source x))))

;; remove id v from lst
(define (remove-id v lst) (remove v lst free-identifier=?))
  
