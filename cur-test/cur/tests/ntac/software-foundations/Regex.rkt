#lang cur

;; example from @dmelcer9, this version (Regex.rkt):
;; - does not name some exp-match MStarApp constructor args (last 2),
;; - so by-apply will not try to infer them, and will instead generate subgoals
;; (this is the old behavior)

(require cur/tests/ntac/rackunit-ntac)

(require cur/stdlib/prop)
(require cur/stdlib/list)
(require cur/stdlib/equality)
(require cur/stdlib/sugar)

(require cur/ntac/base)
(require cur/ntac/standard)
(require cur/ntac/rewrite)

(define-datatype reg-exp (T : (Type 0)) : (Type 0)
  [EmptySet : (reg-exp T)]
  [EmptyStr : (reg-exp T)]
  [Char (t : T) : (reg-exp T)]
  [App (r1 : (reg-exp T)) (r2 : (reg-exp T)) : (reg-exp T)]
  [Union (r1 : (reg-exp T)) (r2 : (reg-exp T)) : (reg-exp T)]
  [Star (r : (reg-exp T)) : (reg-exp T)])

(define-datatype exp-match (T : (Type 0)) : (-> (List T) (reg-exp T) (Type 0))
  [MEmpty : (exp-match T (nil T) (EmptyStr T))]
  [MChar (x : T) : (exp-match T (build-list T x) (Char T x))]
  [MApp (s1 : (List T))
        (re1 : (reg-exp T))
        (s2 : (List T))
        (re2 : (reg-exp T))
        (exp-match T s1 re1)
        (exp-match T s2 re2) 
        : (exp-match T (list-append T s1 s2) (App T re1 re2))]
  [MUnionL (s1 : (List T))
           (re1 : (reg-exp T))
           (re2 : (reg-exp T))
           (exp-match T s1 re1)
           : (exp-match T s1 (Union T re1 re2))]
  [MUnionR (re1 : (reg-exp T))
           (s2 : (List T))
           (re2 : (reg-exp T))
           (exp-match T s2 re2)
           : (exp-match T s2 (Union T re1 re2))]
  [MStar0 (re : (reg-exp T))
          : (exp-match T (nil T) (Star T re))]
  [MStarApp (s1 : (List T))    
            (s2 : (List T))
            (re : (reg-exp T))
            (exp-match T s1 re) ; <- old behavior: to produce subgoals,
            (exp-match T s2 (Star T re)) ; <-      these must be unnamed
            : (exp-match T (list-append T s1 s2) (Star T re))])

(define empty-is-empty
  (ntac (∀ (T : (Type 0)) (s : (List T))  (exp-match T s (EmptySet T)) False)
        (by-intros T s match)
        (by-inversion match)))

; https://coq.inria.fr/library/Coq.Lists.List.html#In
(define/rec/match list-in : [A : Type] [a : A] (List A) -> Type
  [(nil A) => False]
  [(cons A b m) => (Or (== A b a) (list-in A a m))])

(define/rec/match fold : (X : Type) (Y : Type) (f : (-> X Y Y)) [b : Y] (List X) -> Y
  [(nil X) => b]
  [(cons X h t) => (f h (fold X Y f b t))])

(define MUnionInformal
  (ntac (∀ (T : (Type 0))
           (s : (List T))
           (re1 : (reg-exp T))
           (re2 : (reg-exp T))
           (Or (exp-match T s re1) (exp-match T s re2))
           (exp-match T s (Union T re1 re2)))
        (by-intros T s re1 re2 lr)
        (by-destruct lr #:as [(l) (r)])
        ; Subgoal 1
        (by-apply MUnionL)
        by-assumption
        ; Subgoal 2
        (by-apply MUnionR)
        by-assumption))

(define MStarInformal
  (ntac (∀ (T : Type)
           (ss : (List (List T)))
           (re : (reg-exp T))
           (∀ (s : (List T)) (list-in (List T) s ss) (exp-match T s re))
           (exp-match T (fold (List T) (List T) (list-append T) (nil T) ss) (Star T re)))
        (by-intros T ss re H)
        
        (by-induction ss #:as [() (x xs IH)])
        
        ;; Subgoal 1
        (by-apply MStar0)

        ;; Subgoal 2:
        (by-apply MStarApp)

        ;;; H1 of MStarApp
        (by-apply H)
        by-left
        reflexivity
        
        ;;; H2 of MStarApp
        (by-apply IH)
        (by-intros s li)
        (by-apply H)
        by-right
        by-assumption
        ))
