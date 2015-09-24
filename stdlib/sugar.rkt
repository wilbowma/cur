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
    [(_ t1 t2) #`(forall (#,(gensym) : t1) t2)]))

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

(define-syntax define-type
  (syntax-rules ()
    [(_ (name (a : t) ...) body)
     (define name (forall* (a : t) ... body))]
    [(_ name type)
     (define name type)]))

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
    (syntax-case clause (: IH:)
      [((con (a : A) ...) IH: ((x : t) ...) body)
       #'(lambda* (a : A) ... (x : t) ... body)]
      [(e body) #'body])))

;; TODO: Expects clauses in same order as constructors as specified when
;; TODO: inductive D is defined.
(define-syntax (case* syn)
  (syntax-case syn ()
    [(_ D U e P clause* ...)
     #`(elim D U P #,@(map rewrite-clause (syntax->list #'(clause* ...))) e)]))

(define-syntax-rule (define-theorem name prop)
  (define name prop))

(define-syntax (qed stx)
  (syntax-case stx ()
    [(_ t pf)
     (begin
       (unless (type-check/syn? #'pf #'t)
         (raise-syntax-error 'qed "Invalid proof"
           #'pf #'t))
       #'pf)]))

