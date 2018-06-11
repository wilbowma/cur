#lang cur
(require cur/stdlib/bool
         cur/stdlib/prop
         cur/stdlib/sugar
         
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/prop
         
         cur/stdlib/coqeq
         cur/ntac/coqrewrite)

;; tests involving rewrite of a ∀ thm

;; f(b) = b
(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b)
        (λ [fb : Bool] [b : Bool]
           (λ [fx=x : (== Bool fb b)]
             (== Bool fb b)))
        (λ [b : Bool]
          (refl Bool b))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f b) b)))))

;; f(f(b)) = f(b)
(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b)
        (λ [fb : Bool] [b : Bool]
           (λ [fx=x : (== Bool fb b)]
             (== Bool (f fb) (f b))))
        (λ [b : Bool]
          (refl Bool (f b)))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f (f b)) (f b))))))

;; not working
#;(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H (f b))
        (λ [ffb : Bool] [fb : Bool]
           (λ [ffb=fb : (== Bool ffb fb)]
             (== Bool ffb b)))
        (λ [b : Bool]
          (new-elim
           (H b)
           (λ [fb : Bool] [b : Bool]
              (λ [fb=b : (== Bool fb b)]
                (== Bool fb b)))
           (λ [b : Bool]
             (refl Bool (f b)))))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f (f b)) b)))))


;; proof 1, (H b), (H b)
(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (coq= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b) ; (f b) = b
        (λ [b* : Bool]
          (λ [fb=b : (coq= Bool (f b) b*)]
            (coq= Bool (f (f b)) b*)))
        (new-elim
         (H b) ; (f b) = b
         (λ [b* : Bool]
           (λ [fb=b : (coq= Bool (f b) b*)]
             (coq= Bool (f (f b)) (f b*))))
         (coq-refl Bool (f (f b))))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (coq= Bool (f x) x))
        (∀ [b : Bool] (coq= Bool (f (f b)) b)))))

;; proof 2, (H b), (H (f b))
(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (coq= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b) ; (f b) = b
        (λ [b* : Bool]
          (λ [fb=b : (coq= Bool (f b) b*)]
            (coq= Bool (f (f b)) b*)))
        (new-elim
         (H (f b)) ; (f (f b)) = (f b)
         (λ [b* : Bool]
           (λ [fb=b : (coq= Bool (f (f b)) b*)]
             (coq= Bool (f (f b)) b*)))
         (coq-refl Bool (f (f b))))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (coq= Bool (f x) x))
        (∀ [b : Bool] (coq= Bool (f (f b)) b)))))

;; proof 3, with 1 sym
(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (coq= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (coq=-sym Bool (f b) b (H b)) ;  b = (f b)
        (λ [fb : Bool]
          (λ [b=fb : (coq= Bool b fb)]
            (coq= Bool (f fb) b)))
        (new-elim
         (H b) ; (f b) = b
         (λ [b* : Bool]
           (λ [fb=b : (coq= Bool (f b) b*)]
             (coq= Bool (f b) b*)))
         (coq-refl Bool (f b)))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (coq= Bool (f x) x))
        (∀ [b : Bool] (coq= Bool (f (f b)) b)))))

;; proof 4, with 2 sym, want last proof as (refl b)
(:: 
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (coq= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (coq=-sym Bool (f b) b (H b)) ;  b = (f b)
        (λ [fb : Bool]
          (λ [b=fb : (coq= Bool b fb)]
            (coq= Bool (f fb) b))) ; need: (f b) = b
        (new-elim
         (coq=-sym Bool (f b) b (H b)) ; b = (f b)
         (λ [fb : Bool]
           (λ [b=fb : (coq= Bool b fb)]
             (coq= Bool fb b)))
         (coq-refl Bool b))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (coq= Bool (f x) x))
        (∀ [b : Bool] (coq= Bool (f (f b)) b)))))


(define-theorem identity-fn-applied-twice
  (∀ [f : (-> Bool Bool)]
     (-> (∀ [x : Bool] (coq= Bool (f x) x))
         (∀ [b : Bool] (coq= Bool (f (f b)) b))))
  (by-intro f)
  (by-intro H)
  (by-intro b)
  (by-coq-rewrite H b)
  (by-coq-rewrite H b)
  coq-reflexivity
)

(define-theorem negb-invol
  (forall [b : Bool] (coq= Bool (not (not b)) b))
  (by-intro b)
  (by-destruct/elim b)
  simpl
  coq-reflexivity
  ; -----------
  simpl
  coq-reflexivity)


(define-theorem not-applied-twice
  (∀ [f : (-> Bool Bool)]
     (-> (∀ [x : Bool] (coq= Bool (f x) (not x)))
         (∀ [b : Bool] (coq= Bool (f (f b)) b))))
  (by-intro f)
  (by-intro H)
  (by-intro b)
  (by-coq-rewrite H b)
  (by-coq-rewrite H (not b))
  (by-coq-rewrite/thm negb-invol b)
  coq-reflexivity)
