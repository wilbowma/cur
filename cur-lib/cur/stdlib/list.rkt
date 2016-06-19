#lang s-exp "../main.rkt"
(require
 "nat.rkt"
 "maybe.rkt"
 "sugar.rkt")

(provide
 List
 nil
 cons
 list-ref
 length)

(data List : (-> (A : Type) Type)
  (nil : (-> (A : Type) (List A)))
  (cons : (-> (A : Type) A (List A) (List A))))

(define (list-ref (A : Type) (ls : (List A)))
  (match ls
    [(nil (A : Type)) (lambda (n : Nat) (none A))]
    [(cons (A : Type) (a : A) (rest : (List A)))
     (lambda (n : Nat)
       (match n
         [z (some A a)]
         [(s (n-1 : Nat))
          ((recur rest) n-1)]))]))

(define (length (A : Type) (ls : (List A)))
  (match ls
    [(nil (A : Type))
     z]
    [(cons (A : Type) (a : A) (rest : (List A)))
     (s (recur rest))]))

(require cur/stdlib/tactics/base
         cur/stdlib/tactics/standard)

;; XXX Error messages are really bad, I made lots of mistakes and it
;; was very painful to find them.

;; XXX Move to different file
(data ex : (forall (A : Type) (P : (-> A Type)) Type)
      (ex-intro :
                (forall
                 ;; XXX I forgot to include these. It is annoying that
                 ;; I have to
                 (A : Type) (P : (-> A Type))
                 (a : A)
                 (-> (P a)
                     (ex A P)))))

(define-syntax-rule (exists (x : T) P)
  (ex T (λ (x : T) P)))

;; XXX Make a (try x) tactic which does (eapply (ex-intro A P x _))
;; reading A and P from the current goal.

;; XXX Move to nat
(data <= : (-> Nat Nat Type)
      (<=-refl : (forall (n : Nat) (<= n n)))
      (<=-S : (forall (n : Nat) (m : Nat) (-> (<= n m) (<= n (s m))))))

(define (< (n : Nat) (m : Nat)) (<= (s n) m))

;; XXX Move to stdlib base
(data = : (forall (A : Type) (-> A A Type))
      (=-refl : (forall (A : Type) (x : A) (= A x x))))

(define-theorem =-ex-1 (= Nat z (sub1 (add1 z))))
;; XXX I didn't write proof yet and it didn't print out "Unresolved proofs."
;; XXX I used (interactive) and (obvious) worked, but when I put it here, it throws an error
#;(proof (obvious))

(define-theorem length-list-ref
  (forall (A : Type)
          (l : (List A))
          (n : Nat)
          (-> (< n (length A l))
              (exists (a : A)
                      (= (Maybe A)
                         (list-ref A l n)
                         ;; XXX I wrote Some and it said term was
                         ;; ill-typed rather than Some was undefined.
                         (some A a))))))


;; XXX (obvious) crashes
(proof
 (intros (A l)) ;; XXX wish I could write (intros A l)
 ;; XXX Want to do (induction l (interactive)) ;; XXX Or assume a default tactic for new goals
 (intros (n LT))
 ;; XXX doing an (intro) here does something really weird.
 (interactive))
