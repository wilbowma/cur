#lang s-exp "redex-core.rkt"
(require rackunit)

;; TODO: Move to standard library
(define-syntax (-> syn)
  (syntax-case syn ()
    [(_ t1 t2)
     (with-syntax ([(x) (generate-temporaries '(1))])
       #'(forall (x : t1) t2))]))

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

(define-syntax-rule (define-theorem name prop)
  (define (name (x : prop)) T))

(define-syntax-rule (qed thm pf)
  (check-equal? T (thm pf)))

(define-syntax (define-type syn)
  (syntax-case syn (:)
    [(_ (name (x : t) ...) e)
     #'(define name (forall* (x : t) ... e))]
    [(_ id e)
     #'(define id e)]))

;; ---------

(data true : Type (T : true))
(data false : Type)
(data equal : (forall* (A : Type) (B : Type) Type))

;; ---------

(define-syntax (translate syn)
  (syntax-case syn (_t _v Type forall Unv lambda :)
    [(_ _t Type)
     #'(lambda* (x1 : Type) (x2 : Type) (->* x1 x2 Type))]
    [(_ _v Type)
     #'(lambda* (x1 : Type) (x2 : Type) (equal x1 x2))]
    [(_ e (forall (x : A) B))
     #'(lambda* (f1 : (forall (x : A) B)) (f2 : (forall (x : A) B))
                (forall* (x1 : A) (x2 : A) (xr : ((translate _t A) x1 x2))
                         ((translate e B) (f1 x1) (f2 x2))))]
    [(_ e (lambda (x : A) B))
     #'(lambda* (f1 : (forall (x : A) B)) (f2 : (forall (x : A) B))
                (forall* (x1 : A) (x2 : A) (xr : ((translate _t A) x1 x2))
                         ((translate e B) (f1 x1) (f2 x2))))]
    [(_ e (f a))
     ;; Not sure this is quite right; probably need to rename a
     #'((translate e f) a a (translate e a))]
    [(_ e x)
     ;; Not sure this is quite right; Racket's hygiene might `save' me.
     #'(xr)]
    [_ (raise-syntax-error "translate undefined for" syn)]))

(define-theorem thm:type_t ((translate _t Type) Type Type))
(qed thm:type_t (translate _v Type))
(translate _v Type)
((translate _t Type) Type Type)

((translate _v Type) true false)
