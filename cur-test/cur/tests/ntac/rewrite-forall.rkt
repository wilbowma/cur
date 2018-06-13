#lang cur
(require cur/stdlib/bool
         cur/stdlib/equality
         cur/stdlib/sugar

         cur/ntac/base
         cur/ntac/standard

         cur/ntac/rewrite)

;; tests involving rewrite of a ∀ thm

;; f(b) = b
(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (ML-= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b)
        (λ [fb : Bool] [b : Bool]
           (λ [fx=x : (ML-= Bool fb b)]
             (ML-= Bool fb b)))
        (λ [b : Bool]
          (ML-refl Bool b))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (ML-= Bool (f x) x))
        (∀ [b : Bool] (ML-= Bool (f b) b)))))

;; f(f(b)) = f(b)
(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (ML-= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b)
        (λ [fb : Bool] [b : Bool]
           (λ [fx=x : (ML-= Bool fb b)]
             (ML-= Bool (f fb) (f b))))
        (λ [b : Bool]
          (ML-refl Bool (f b)))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (ML-= Bool (f x) x))
        (∀ [b : Bool] (ML-= Bool (f (f b)) (f b))))))

;; not working
#;(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (ML-= Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H (f b))
        (λ [ffb : Bool] [fb : Bool]
           (λ [ffb=fb : (ML-= Bool ffb fb)]
             (ML-= Bool ffb b)))
        (λ [b : Bool]
          (new-elim
           (H b)
           (λ [fb : Bool] [b : Bool]
              (λ [fb=b : (ML-= Bool fb b)]
                (ML-= Bool fb b)))
           (λ [b : Bool]
             (refl Bool (f b)))))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (ML-= Bool (f x) x))
        (∀ [b : Bool] (ML-= Bool (f (f b)) b)))))


;; proof 1, (H b), (H b)
(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b) ; (f b) = b
        (λ [b* : Bool]
          (λ [fb=b : (== Bool (f b) b*)]
            (== Bool (f (f b)) b*)))
        (new-elim
         (H b) ; (f b) = b
         (λ [b* : Bool]
           (λ [fb=b : (== Bool (f b) b*)]
             (== Bool (f (f b)) (f b*))))
         (refl Bool (f (f b))))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f (f b)) b)))))

;; proof 2, (H b), (H (f b))
(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (H b) ; (f b) = b
        (λ [b* : Bool]
          (λ [fb=b : (== Bool (f b) b*)]
            (== Bool (f (f b)) b*)))
        (new-elim
         (H (f b)) ; (f (f b)) = (f b)
         (λ [b* : Bool]
           (λ [fb=b : (== Bool (f (f b)) b*)]
             (== Bool (f (f b)) b*)))
         (refl Bool (f (f b))))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f (f b)) b)))))

;; proof 3, with 1 sym
(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (sym Bool (f b) b (H b)) ;  b = (f b)
        (λ [fb : Bool]
          (λ [b=fb : (== Bool b fb)]
            (== Bool (f fb) b)))
        (new-elim
         (H b) ; (f b) = b
         (λ [b* : Bool]
           (λ [fb=b : (== Bool (f b) b*)]
             (== Bool (f b) b*)))
         (refl Bool (f b)))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f (f b)) b)))))

;; proof 4, with 2 sym, want last proof as (refl b)
(::
 (λ [f : (-> Bool Bool)]
   (λ [H : (∀ [x : Bool] (== Bool (f x) x))]
     (λ [b : Bool]
       (new-elim
        (sym Bool (f b) b (H b)) ;  b = (f b)
        (λ [fb : Bool]
          (λ [b=fb : (== Bool b fb)]
            (== Bool (f fb) b))) ; need: (f b) = b
        (new-elim
         (sym Bool (f b) b (H b)) ; b = (f b)
         (λ [fb : Bool]
           (λ [b=fb : (== Bool b fb)]
             (== Bool fb b)))
         (refl Bool b))))))
 (∀ [f : (-> Bool Bool)]
    (-> (∀ [x : Bool] (== Bool (f x) x))
        (∀ [b : Bool] (== Bool (f (f b)) b)))))


(define-theorem identity-fn-applied-twice
  (∀ [f : (-> Bool Bool)]
     (-> (∀ [x : Bool] (== Bool (f x) x))
         (∀ [b : Bool] (== Bool (f (f b)) b))))
  (by-intro f)
  (by-intro H)
  (by-intro b)
  (by-rewrite H b)
  (by-rewrite H b)
  reflexivity
)

(define-theorem negb-invol
  (forall [b : Bool] (== Bool (not (not b)) b))
  (by-intro b)
  (by-destruct/elim b)
  simpl
  reflexivity
  ; -----------
  simpl
  reflexivity)


(define-theorem not-applied-twice
  (∀ [f : (-> Bool Bool)]
     (-> (∀ [x : Bool] (== Bool (f x) (not x)))
         (∀ [b : Bool] (== Bool (f (f b)) b))))
  (by-intro f)
  (by-intro H)
  (by-intro b)
  (by-rewrite H b)
  (by-rewrite H (not b))
  (by-rewrite/thm negb-invol b)
  reflexivity)
