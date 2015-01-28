#lang s-exp "cur-redex.rkt"
;; Ignore this file.
(require rackunit racket/trace (for-syntax racket/syntax))

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
(data * : (forall* (a : Type) (b : Type) Type)
      (prod : (forall* (a : Type) (b : Type) (* a b))))
;; ---------
(begin-for-syntax
  (define (rename_id i x)
    (format-id x "~a~a" x i)))
(define-syntax (rename syn)
  (syntax-case syn (Type forall Unv lambda :)
    [(_ i ls Type) #'Type]
    [(_ i ls (Unv n)) #'(Unv n)]
    [(_ i (xr ...) (lambda (x : t) e))
     #'(lambda (x : (rename i (xr ...) t))
         (rename i (xr ... x) e))]
    [(_ i (xr ...) (forall (x : t) e))
     #'(forall (x : (rename i (xr ...) t))
               (rename i (xr ... x) e))]
    [(_ i ls (e1 e2))
     #'((rename i ls e1) (rename i ls e2))]
    [(_ i ls x)
     (if (member (syntax->datum #'x) (syntax->datum #'ls))
       #'x
       (rename_id (syntax->datum #'i) #'x))]))
(define-syntax (translate syn)
  (syntax-case syn (_t _v Type forall Unv lambda : data)
    [(_ _t Type)
     #'(lambda* (x1 : Type) (x2 : Type) (->* x1 x2 Type))]
    [(_ _v Type)
     #'(lambda* (x1 : Type) (x2 : Type) (equal x1 x2))]
    [(_ e (forall (x : A) B))
     (let ([x1 (rename_id 1 #'x)]
           [x2 (rename_id 2 #'x)]
           [xr (rename_id 'r #'x)])
       #`(lambda* (f1 : (rename 1 () (forall (x : A) B)))
                  (f2 : (rename 2 () (forall (x : A) B)))
                  (forall* (#,x1 : (rename 1 () A)) (#,x2 : (rename 2 () A))
                           (#,xr : ((translate _t A) #,x1 #,x2))
                           ((translate e B) (f1 #,x1) (f2 #,x2)))))]
    [(_ e (lambda (x : A) B))
     (let ([x1 (rename_id 1 #'x)]
           [x2 (rename_id 2 #'x)]
           [xr (rename_id 'r #'x)])
       #`(lambda* (f1 : (rename 1 () (forall (x : A) B)))
                  (f2 : (rename 2 () (forall (x : A) B)))
                 (forall* (#,x1 : (rename 1 () A))
                          (#,x2 : (rename 2 () A))
                          (#,xr : ((translate _t A) #,x1 #,x2))
                          ((translate e B) (f1 #,x1) (f2 #,x2)))))]
    [(_ e (data id : t (c : tc) ...))
     (let ([t #`(data #,(rename_id 'r #'id) : (translate e t)
                     ((translate e c) : (translate e tc)) ...) ])
       t)]
    [(_ e (f a))
     #`((translate e f) (rename 1 () a) (rename 2 () a) (translate e a))]
    [(_ e x)
     ;; Not sure this is quite right; Racket's hygiene might `save' me.
     (rename_id 'r #'x)]
    [_ (raise-syntax-error "translate undefined for" syn)]))

(define-theorem thm:type_t ((translate _t Type) Type Type))
(qed thm:type_t (translate _v Type))
(translate _v Type)
((translate _t Type) Type Type)

((translate _v Type) true false)

#;(define true1 true)
#;(define true2 true)

(data nat : Type
      (z : nat)
      (s : (-> nat nat)))

(define nat1 nat)
(define nat2 nat)
(define natr (lambda* (n1 : nat) (n2 : nat) true))

(data heap : Type)
(define heap1 heap)
(define heap2 heap)
(data heap-equal : (forall* (h1 : heap) (h2 : heap) Type))
(define heapr natr)

(define-type (pre (h : heap)) Type)
(define pre1 pre)
(define pre2 pre)
(define prer (translate _v (forall (h : heap) Type)))
prer

(define-type (monad (s : pre)
                    (tp : (-> pre Type))
                    (unit : (forall (x : nat) (tp (lambda (h : heap) true)))))
            (-> heap (tp s)))

#;(define monad-type
  (forall (s : pre)
  (forall (tp : (forall (p : pre) Type))
  (forall (unit : (forall (x : nat) (tp (lambda (h : heap)
                                                      true))))
                      (forall (h : heap) (tp s))))))
;monad-type
#;(translate _v (forall (s : pre)
              (forall (tp : (forall (p : pre) Type))
              (forall (unit : (forall (x : nat) (tp (lambda (h : heap) true))))
                      (forall (h : heap) (tp s))))))
;; and : (forall (A : Type) (B : Type) Type)
(data and : (forall* (A : Type) (B : Type) Type)
      (conj : (forall* (A : Type) (B : Type) (a : A) (b : B) (and A B))))
((translate _v (forall (A : Type) (forall (B : Type) Type))) and and)
;; conj : (forall (A : Type) (B : Type) (a : A) (b : B) (and A B))
((translate _v (forall (A : Type) (forall (B : Type) 
                                          (forall (a : A) (forall (b :
                                                                     B)
                                                                  ((and
                                                                     A)
                                                                   B))))))
 conj conj)

(translate _v T)
((translate _v true) T T)
((translate _v Type) true true)
