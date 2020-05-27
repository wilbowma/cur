#lang cur
;; See https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html

(require
  cur/stdlib/ascii
  cur/stdlib/bool
  cur/stdlib/sugar
  cur/stdlib/equality
  cur/ntac/base
  cur/ntac/standard
  cur/ntac/rewrite)

;; =========
;;  HELPERS
;; =========

; Option
(define-datatype option [A : Type] : Type
  [Some* : (-> A (option A))]
  [None* : (option A)])

(define-implicit Some = Some* 1)
(define-implicit None = None* 1)

; Total map
(define (total-map [A : Type]) (-> String A))
(define (t-empty_ [A : Type] [v : A] [s : String]) v)
(define-implicit t-empty = t-empty_ 1)
(define (t-update_ [A : Type] [m : (total-map A)] [x : String] [v : A])
  (λ [y : String] (if (string-equal? x y) v (m y))))
(define-implicit t-update = t-update_ 1)

; Partial map
(define (partial-map [A : Type]) (total-map (option A)))
(define (empty_ [A : Type]) (t-empty (None A)))
(define-implicit empty = empty_ 1)
(define (update_ [A : Type] [m : (partial-map A)] [x : String] [v : (option A)])
  (λ [y : String] (if (string-equal? x y) v (m y))))
(define-implicit update = update_ 1)

; Relation
(define (relation [X : Type])
    (-> X X Prop))

; Multi
(define-datatype multi [X : Type] [R : (relation X)] : (relation X)
  [multi-refl : (∀ [x : X] (multi X R x x))]
  [multi-step : (∀ [x : X] [y : X] [z : X]
                   (-> (R x y) (multi X R y z) (multi X R x z)))])

;; ========
;;  SYNTAX
;; ========

;; -------
;;  Types
;; -------
(define-datatype ty : Type
  [Bool : ty]
  [Arrow : (-> ty ty ty)])

;; -------
;;  Terms
;; -------
(define-datatype tm : Type
  [var : (-> String tm)]                  ; variable:       x
  [app : (-> tm tm tm)]                   ; application:    t1 t2
  [abs : (-> String ty tm tm)]            ; abstraction:    \x:T1.t2
  [tru : tm]                              ; constant true:  tru
  [fls : tm]                              ; constant false: fls
  [test : (-> tm tm tm tm)])              ; conditional:    test t1 then t2 else t3

;; ----------
;;  Examples
;; ----------
(define x "x")
(define y "y")
(define z "z")

; idB = \x:Bool. x
(define idB (abs x Bool (var x)))

; idBB = \x:Bool->Bool. x
(define idBB (abs x (Arrow Bool Bool) (var x)))

; idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x
(define idBBBB (abs x (Arrow (Arrow Bool Bool) (Arrow Bool Bool)) (var x)))

; k = \x:Bool. \y:Bool. x
(define k (abs x Bool (abs y Bool (var x))))

; notB = \x:Bool. test x then fls else tru
(define notB (abs x Bool (test (var x) fls tru)))

;; =======================
;;  OPERATIONAL SEMANTICS
;; =======================

;; --------
;;  Values
;; --------
(define-datatype value : (-> tm Prop)
  [v-abs : (∀ [x : String] [T : ty] [t : tm] (value (abs x T t)))]
  [v-tru : (value tru)]
  [v-fls : (value fls)])

;; --------------
;;  Substitution
;; --------------

;; TODO
;; Technical note: Substitution becomes trickier to define if we consider the
;; case where s, the term being substituted for a variable in some other term,
;; may itself contain free variables.
(define/rec/match subst-tmp : [x : String] [s : tm] tm -> tm
  [(var xp) => (if (string-equal? x xp)
                   s
                   (var xp))]
  [(abs xp T t1) => (if (string-equal? x xp)
                        (abs xp T t1)
                        (abs xp T (subst-tmp x s t1)))]
  [tru => tru]
  [fls => fls]
  [(test t1 t2 t3) => (test (subst-tmp x s t1) (subst-tmp x s t2) (subst-tmp x s t3))]
  [(app t1 t2) => (app t1 t2)])

(define subst subst-tmp)

;; -----------
;;  Reduction
;; -----------
(define-datatype step : (-> tm tm Prop)
  [ST-AppAbs : (∀ [x : String] [T : ty] [t12 : tm] [v2 : tm]
                  (-> (value v2)
                      (step (app (abs x T t12) v2) (subst x v2 t12))))]
  [ST-App1 : (∀ [t1 : tm] [t1p : tm] [t2 : tm]
                (-> (step t1 t1p)
                    (step (app t1 t2) (app t1p t2))))]
  [ST-App2 : (∀ [v1 : tm] [t2 : tm] [t2p : tm]
                (-> (value v1)
                    (step t2 t2p)
                    (step (app v1 t2) (app v1 t2p))))]
  [ST-TestTru : (∀ [t1 : tm] [t2 : tm]
                   (step (test tru t1 t2) t1))]
  [ST-TestFls : (∀ [t1 : tm] [t2 : tm]
                   (step (test fls t1 t2) t2))]
  [ST-Test : (∀ [t1 : tm] [t1p : tm] [t2 : tm] [t3 : tm]
                (-> (step t1 t1p)
                    (step (test t1 t2 t3) (test t1p t2 t3))))])

(define-syntax -->
  (syntax-parser
    [(_ t1 t2) #'(step t1 t2)]))

(define-syntax -->*
  (syntax-parser
    [(_ t1 t2) #'((multi tm step) t1 t2)]))

;; ----------
;;  Examples
;; ----------

; (\x:Bool→Bool. x) (\x:Bool. x) -->* \x:Bool. x
#;(define-theorem step-example-1
  (-->* (app idBB idB) idB)
    ; TODO
    ; https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.eapply
    ; The tactic eapply behaves like apply but it does not fail when no
    ; instantiations are deducible for some variables in the premises. Rather,
    ; it turns these variables into existential variables which are variables
    ; still to instantiate (see Existential variables). The instantiation is
    ; intended to be found later in the proof.
  (by-apply multi-step) ; by-apply: could not infer instantiation of: multi-step; try explicit #:with or #:with-var args?
  (by-apply ST-AppAbs)
  (by-apply v-abs)
  simpl
  (by-apply multi-refl))

(define step-example-1
  (ann (multi-step tm step (app idBB idB) idB idB
                   (ST-AppAbs x (Arrow Bool Bool) (var x) idB (v-abs x Bool (var x)))
                   (multi-refl tm step idB))
       : (-->* (app idBB idB) idB)))

; (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x)) -->* \x:Bool. x
#;(define-theorem step-example-2
  (-->* (app idBB (app idBB idB)) idB)
  (by-apply multi-step) ; by-apply: could not infer instantiation of: multi-step; try explicit #:with or #:with-var args?
  (by-apply ST-App2)
  (by-apply ST-AppAbs)
  (by-apply multi-step)
  (by-apply ST-AppAbs)
  simpl
  auto
  simpl
  (by-apply multi-refl))

(define step-example-2
  (ann (multi-step tm step (app idBB (app idBB idB)) (app idBB idB) idB
                   (ST-App2 idBB (app idBB idB) idB
                            (v-abs x (Arrow Bool Bool) (var x))
                            (ST-AppAbs x (Arrow Bool Bool) (var x) idB (v-abs x Bool (var x))))
                   step-example-1)
       : (-->* (app idBB (app idBB idB)) idB)))

; (\x:Bool->Bool. x) (\x:Bool. test x then fls else tru) tru -->* fls
#;(define-theorem step-example-3
  (-->* (app (app idBB notB) tru) fls)
  (by-apply multi-step) ; by-apply: could not infer instantiation of: multi-step; try explicit #:with or #:with-var args?
  (by-apply ST-App1)
  (by-apply ST-AppAbs)
  auto
  simpl
  (by-apply multi-step)
  (by-apply ST-AppAbs)
  auto
  simpl
  (by-apply multi-step)
  (by-apply ST-TestTru)
  (by-apply multi-refl))

(define step-example-3
  (ann (multi-step tm step (app (app idBB notB) tru) (app notB tru) fls
                   (ST-App1 (app idBB notB) notB tru
                            (ST-AppAbs x (Arrow Bool Bool) (var x) notB (v-abs x Bool (test (var x) fls tru))))
                   (multi-step tm step (app notB tru) (test tru fls tru) fls
                               (ST-AppAbs x Bool (test (var x) fls tru) tru
                                          v-tru)
                               (multi-step tm step (test tru fls tru) fls fls
                                           (ST-TestTru fls tru)
                                           (multi-refl tm step fls))))
       : (-->* (app (app idBB notB) tru) fls)))

; (\x:Bool -> Bool. x) ((\x:Bool. test x then fls else tru) tru) -->* fls
#;(define-theorem step-example-4
  (-->* (app idBB (app notB tru)) fls)
  (by-apply multi-step) ; by-apply: could not infer instantiation of: multi-step; try explicit #:with or #:with-var args?
  (by-apply ST-App2)
  (by-apply ST-AppAbs)
  auto
  simpl
  (by-apply multi-step)
  (by-apply ST-App2)
  auto
  (by-apply ST-TestTru)
  (by-apply multi-step)
  (by-apply ST-AppAbs)
  auto
  simpl
  (by-apply multi-refl))

(define step-example-4
  (ann (multi-step tm step (app idBB (app notB tru)) (app idBB (test tru fls tru)) fls
                   (ST-App2 idBB (app notB tru) (test tru fls tru)
                            (v-abs x (Arrow Bool Bool) (var x))
                            (ST-AppAbs x Bool (test (var x) fls tru) tru
                                       v-tru))
                   (multi-step tm step (app idBB (test tru fls tru)) (app idBB fls) fls
                               (ST-App2 idBB (test tru fls tru) fls
                                        (v-abs x (Arrow Bool Bool) (var x))
                                        (ST-TestTru fls tru))
                               (multi-step tm step (app idBB fls) fls fls
                                           (ST-AppAbs x (Arrow Bool Bool) (var x) fls
                                                      v-fls)
                                           (multi-refl tm step fls))))
       : (-->* (app idBB (app notB tru)) fls)))

(define step-example-5
  (ann (multi-step tm step (app (app idBBBB idBB) idB) (app idBB idB) idB
                   (ST-App1 (app idBBBB idBB) idBB idB
                            (ST-AppAbs x (Arrow (Arrow Bool Bool) (Arrow Bool Bool)) (var x) idBB
                                       (v-abs x (Arrow Bool Bool) (var x))))
                   (multi-step tm step (app idBB idB) idB idB
                               (ST-AppAbs x (Arrow Bool Bool) (var x) idB
                                          (v-abs x Bool (var x)))
                               (multi-refl tm step idB)))
       : (-->* (app (app idBBBB idBB) idB) idB)))

;; ========
;;  Typing
;; ========

;; ----------
;;  Contexts
;; ----------
(define context (partial-map ty))

;; --------
;;  Typing
;; --------
(define-datatype has-type : (-> context (-> tm (-> ty Prop)))
  [T-Var : (∀ [Gamma : context] [x : String] [T : ty]
         (-> (== (option ty) (Gamma x) (Some T))
             (has-type Gamma (var x) T)))]
  [T-Abs : (∀ [Gamma : context] [x : String] [T11 : ty] [T12 : ty] [t12 : tm]
              (-> (has-type (update Gamma x (Some T11)) t12 T12)
                  (has-type Gamma (abs x T11 t12) (Arrow T11 T12))))]
  [T-App : (∀ [T11 : ty] [T12 : ty] [Gamma : context] [t1 : tm] [t2 : tm]
              (-> (has-type Gamma t1 (Arrow T11 T12))
                  (has-type Gamma t2 T11)
                  (has-type Gamma (app t1 t2) T12)))]
  [T-Tru : (∀ [Gamma : context]
              (has-type Gamma tru Bool))]
  [T-Fls : (∀ [Gamma : context]
              (has-type Gamma fls Bool))]
  [T-Test : (∀ [t1 : tm] [t2 : tm] [t3 : tm] [T : ty] [Gamma : context]
               (-> (has-type Gamma t1 Bool)
                   (has-type Gamma t2 T)
                   (has-type Gamma t3 T)
                   (has-type Gamma (test t1 t2 t3) T)))])

; where "Gamma '⊢' t '∈' T" := (has_type Gamma t T)
; well, there was an effort...
(define-syntax ⊢
  (syntax-parser
    [(_ Gamma t T) #'(has-type Gamma t T)]))

;; ----------
;;  Examples
;; ----------

(define-theorem typing-example-1
  (⊢ (empty) (abs x Bool (var x)) (Arrow Bool Bool))
  (by-apply T-Abs)
  (by-apply T-Var)
  reflexivity)

(define typing-example-1p
  (ann (T-Abs (empty_ ty) x Bool Bool (var x)
              (T-Var (update (empty_ ty) x (Some Bool)) x Bool
                     (refl (option ty) (Some Bool))))
       : (⊢ (empty) (abs x Bool (var x)) (Arrow Bool Bool))))

(define typing-example-2
  (ann (T-Abs (empty_ ty) x Bool (Arrow (Arrow Bool Bool) Bool) (abs y (Arrow Bool Bool) (app (var y) (app (var y) (var x))))
              (T-Abs (update (empty_ ty) x (Some Bool)) y (Arrow Bool Bool) Bool (app (var y) (app (var y) (var x)))
                     (T-App Bool Bool (update (update (empty_ ty) x (Some Bool)) y (Some (Arrow Bool Bool))) (var y) (app (var y) (var x))
                            (T-Var (update (update (empty_ ty) x (Some Bool)) y (Some (Arrow Bool Bool))) y (Arrow Bool Bool)
                                   (refl (option ty) (Some (Arrow Bool Bool))))
                            (T-App Bool Bool (update (update (empty_ ty) x (Some Bool)) y (Some (Arrow Bool Bool))) (var y) (var x)
                                   (T-Var (update (update (empty_ ty) x (Some Bool)) y (Some (Arrow Bool Bool))) y (Arrow Bool Bool)
                                          (refl (option ty) (Some (Arrow Bool Bool))))
                                   (T-Var (update (update (empty_ ty) x (Some Bool)) y (Some (Arrow Bool Bool))) x Bool
                                          (refl (option ty) (Some Bool)))))))
       : (⊢ (empty) (abs x Bool (abs y (Arrow Bool Bool) (app (var y) (app (var y) (var x))))) (Arrow Bool (Arrow (Arrow Bool Bool) Bool)))))
