#lang s-exp "redex-curnel.rkt"
(provide ->
         ->*
         forall*
         lambda*
         #%app
         define
         case*
         define-theorem
         qed)

(require (only-in "cur-redex.rkt" [#%app real-app]
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

(define-syntax (define syn)
  (syntax-case syn ()
    [(define (name (x : t) ...) body)
     #'(real-define name (lambda* (x : t) ... body))]
    [(define id body)
     #'(real-define id body)]))

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

(define-syntax-rule (qed thm pf)
  ((lambda (x : thm) T) pf))
