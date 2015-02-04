#lang s-exp "../redex-curnel.rkt"
(provide ->
         ->*
         forall*
         lambda*
         #%app
         define
         case*
         define-type
         define-theorem
         qed
         real-app
         define-rec)

(require (only-in "../redex-curnel.rkt" [#%app real-app]
                  [define real-define]))


(define-syntax (-> syn)
  (syntax-case syn ()
    [(_ t1 t2)
     (with-syntax ([(x) (generate-temporaries '(1))])
       #`(forall (x : t1) t2))]))

(define-syntax ->*
  (syntax-rules ()
    [(->* a) a]
    [(->* a a* ...)
     (-> a (->* a* ...))]))

(define-syntax forall*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (forall (a : t)
        (forall* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax lambda*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (lambda (a : t)
       (lambda* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax (#%app syn)
  (syntax-case syn ()
    [(_ e1 e2)
     #'(real-app e1 e2)]
    [(_ e1 e2 e3 ...)
     #'(#%app (#%app e1 e2) e3 ...)]))

(define-syntax-rule (define-type (name (a : t) ...) body)
  (define name (forall* (a : t) ... body)))

(define-syntax (define syn)
  (syntax-case syn ()
    [(define (name (x : t) ...) body)
     #'(real-define name (lambda* (x : t) ... body))]
    [(define id body)
     #'(real-define id body)]))

(define-syntax (define-rec syn)
  (syntax-case syn (:)
    [(_ (name (a : t) ... : t_res) body)
     #'(define name (fix (name : (forall* (a : t) ... t_res))
                      (lambda* (a : t) ... body)))]))
(begin-for-syntax
  (define (rewrite-clause clause)
    (syntax-case clause (:)
      [((con (a : A) ...) body) #'(con (lambda* (a : A) ... body))]
      [(e body) #'(e body)])))

(define-syntax (case* syn)
  (syntax-case syn ()
    [(_ e clause* ...)
     #`(case e #,@(map rewrite-clause (syntax->list #'(clause* ...))))]))

(define-syntax-rule (define-theorem name prop)
  (define name prop))

;; TODO: Current implementation doesn't do beta/eta while type-checking
;; because reasons. So manually insert a run in the type annotation
(define-syntax-rule (qed thm pf)
  ((lambda (x : (run thm)) Type) pf))
