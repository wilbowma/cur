#lang s-exp "redex-core.rkt"

(define-syntax (-> syn)
  (syntax-case syn ()
    [(_ t1 t2)
     (with-syntax ([(x) (generate-temporaries '(1))])
       #'(forall (x : t1) t2))]))

(data true : Type
  (TT : true))

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

(lambda (nat : Type)
  ((lambda (x : (forall (y : Type) Type)) (x nat))
   (lambda (y : Type) y)))

(lambda (nat : Type) nat)

(lambda (y : (-> nat nat))
  (lambda (x : nat) (y x)))

(define y (lambda (x : true) x))
(define (y1 (x : true)) x)
y1

(define (y2 (x1 : true) (x2 : true)) x1)
(y2 TT TT)
