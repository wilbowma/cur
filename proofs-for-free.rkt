#lang s-exp "redex-curnel.rkt"
(require "stdlib/sugar.rkt" "stdlib/prop.rkt")

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
  (syntax-parse (cur-expand syn)
    ;; TODO: Need to add these to a literal set and export it
    ;; Or, maybe redefine syntax-parse
    #:literals (lambda forall data real-app case Type)
    [(_ Type)
     #'(lambda* (x1 : Type) (x2 : Type) (->* x1 x2 Type))]
    [(_ (forall (x : A) B))
     (let ([x1 (rename_id 1 #'x)]
           [x2 (rename_id 2 #'x)]
           [xr (rename_id 'r #'x)])
       #`(lambda* (f1 : (rename 1 () (forall (x : A) B)))
                  (f2 : (rename 2 () (forall (x : A) B)))
                  (forall* (#,x1 : (rename 1 () A)) (#,x2 : (rename 2 () A))
                           (#,xr : ((translate A) #,x1 #,x2))
                           ((translate B) (f1 #,x1) (f2 #,x2)))))]
    [(_ (lambda (x : A) B))
     (let ([x1 (rename_id 1 #'x)]
           [x2 (rename_id 2 #'x)]
           [xr (rename_id 'r #'x)])
       #`(lambda* (f1 : (rename 1 () (forall (x : A) B)))
                  (f2 : (rename 2 () (forall (x : A) B)))
                 (forall* (#,x1 : (rename 1 () A))
                          (#,x2 : (rename 2 () A))
                          (#,xr : ((translate A) #,x1 #,x2))
                          ((translate B) (f1 #,x1) (f2 #,x2)))))]
    [(_ (data id : t (c : tc) ...))
     (let ([t #`(data #,(rename_id 'r #'id) : (translate t)
                     ((translate c) : (translate tc)) ...)])
       t)]
    [(_ (f a))
     #`((translate f) (rename 1 () a) (rename 2 () a) (translate a))]
    [(_ x)
     ;; TODO: Look up x and generate the relation. Otherwise I need to
     ;; manually translate all dependencies.
     ;; Not sure this is quite right; Racket's hygiene might `save' me.
     (rename_id 'r #'x)]
    [_ (raise-syntax-error "translate undefined for" syn)]))

(define-type X Type)
(define X1 X)
(define X2 X)
(define (Xr (x1 : X) (x2 : X)) true)

;; The type of a CPS function
(define-type CPSf (forall* (ans : Type) (k : (-> X ans)) ans))

(define (CPSf-relation (f1 : CPSf) (f2 : CPSf))
  (translate (forall* (ans : Type) (k : (-> X ans)) ans))
(module+ test
  (require rackunit)
  (check-equal?
    (translate (forall* (ans : Type) (k : (-> X ans)) ans))
    (forall* (ans1 : Type) (ans2 : Type) (ansr : (->* ans1 ans2 Type))
      (forall* (k1 : (-> X ans1)) (k2 : (-> X ans2))
        (kr : (forall* (_1 : X) (_2 : X) (_r : (Xr _1 _2))
                (ansr (k1 _1) (k2 _2))))
      (ansr (f1 ans1 k1) (f2 ans2 k2)))))))

;; By parametricity, every CPSf is related it itself in the CPS relation
(define-type paramCPSf (forall* (f : CPSf) (CPSf-relation f f)))
(define (id (X : Type) (x : X)) x)

(define-theorem thm:cont-shuffle
  (forall* (f : CPSf)
           (ans : Type)
           (ansr : (-> ans ans Type))
           (k : (-> X ans))
    (ansr (f ans k) (k (f ans (id ans))))))

#;(define (rel (x1 : X) (x2 : X))
  (and (Xr x1 x2)
    ))

#;(paramCPSf f X X rel k k)
