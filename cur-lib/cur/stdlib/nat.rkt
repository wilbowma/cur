#lang s-exp "../main.rkt"

;; TODO: override (all-defined-out) to enable exporting these properly.
(provide #%datum Nat elim-Nat
         z s (for-syntax z s ~Nat)
         add1 sub1 plus minus mult zero? exp square nat-equal? even? <=)

(require "datum.rkt" "sugar.rkt" "bool.rkt")

(define-datatype Nat : Type
  [z : Nat]
  [s : (-> Nat Nat)])

(begin-for-syntax
  (provide nat->unary nat-datum)
  (define (nat->unary n)
    (if (zero? n)
        #`z
        #`(s #,(nat->unary (sub1 n)))))

  (define (nat-datum syn f)
    (syntax-parse syn
      [x:nat
       (nat->unary (syntax->datum #'x))]
      [_ (f syn)]))

  (current-datum nat-datum))

(define (add1 (n : Nat)) (s n))

(define/rec/match sub1 : Nat -> Nat
  [z => z]
  [(s x) => x])

;; plus, using elim-Nat
#;(define plus
  #;(λ [n : Nat]
     (elim-Nat n
               (λ [x : Nat] (→ Nat Nat))
               (λ [m : Nat] m)
               (λ [x : Nat]
                 (λ [pm : (→ Nat Nat)]
                   (λ [x : Nat]
                     (s (pm x)))))))
  (λ [n : Nat][n2 : Nat]
     (elim-Nat n
               (λ [x : Nat] Nat)
               n2
               (λ [x : Nat]
                 (λ [pm : Nat]
                   (s pm)))))
    )

;; plus, using elim-Nat, unrolled
#;(define plus
  (λ [n : Nat][n2 : Nat]
     (elim-Nat n
               (λ [x : Nat] Nat)
               n2
               (λ [x : Nat]
                 (λ [pm : Nat]
                   (s
                    (elim-Nat x
                              (λ [x : Nat] Nat)
                              n2
                              (λ [x : Nat]
                                (λ [pm : Nat]
                                  (s
                                   (elim-Nat x
                                             (λ [x : Nat] Nat)
                                             n2
                                             (λ [x : Nat]
                                               (λ [pm : Nat]
                                                 (s pm)))))))))))))
  )


;; plus, unrolling recursive function call
#;(define plus
#;  (λ [n1 : Nat] [n2 : Nat]
     (match n1 #:return Nat
      [z n2]
      [(s x)
       (s
        ((λ [n1 : Nat] [n2 : Nat]
            (match n1 #:return Nat
                   [z n2]
                   [(s x)
                    (s
                     ((λ [n1 : Nat] [n2 : Nat]
                         (match n1 #:return Nat
                          [z n2]
                          [(s x)
                           (s n2)]))
                      x n2))]))
         x n2))]))
  (λ [n1 : Nat] [n2 : Nat]
     (match n1 #:return Nat
      [z n2]
      [(s x)
       (s
        (match x #:return Nat
               [z n2]
               [(s x)
                (s
                 (match x #:return Nat
                            [z n2]
                            [(s x)
                             (s n2)]))]))])))


; current working plus:
#;(define (plus [n1 : Nat] [n2 : Nat])
  (match n1 #:return Nat
   [z n2]
   [(s x) (s (plus x n2))]))

;; plus as a macro + define-red
#;(define-red eval-plus
  [(#%plain-app ~z n) ~> n]
  [(#%plain-app (~s x) n) ~> (s (plus x n))])
#;(define-syntax eval-plus
  (syntax-parser
    [(_ ~z n2) #'n2]
    [(_ (~s x) n2) #'(s (plus x n2))]
    [debug #:do[(printf "plus: ~a\n" (syntax->datum #'debug))] #:when #f #'debug]
    [(_ n1 n2) #`(#,(mk-reflected #'eval-plus) n1 n2)]))
    
#;(define-typed-syntax plus
  [(_ n1 n2) ≫
   [⊢ n1 ≫ n1- ⇐ Nat]
   [⊢ n2 ≫ n2- ⇐ Nat]
   ------------------
   [⊢ (eval-plus n1- n2-) ⇒ Nat]])

(define/rec/match plus : Nat [n : Nat] -> Nat
  [z => n]
  [(s x) => (s (plus x n))])

(define/rec/match minus : Nat Nat -> Nat
  [z _ => z]
  [(s n-1) z => (s n-1)]
  [(s n-1) (s m-1) => (minus n-1 m-1)])

;; mult, using elim-Nat
#;(define mult
  (λ [m : Nat][n : Nat]
     (elim-Nat m
               (λ [x : Nat] Nat)
               z
               (λ [x : Nat]
                 (λ [pm : Nat]
                   (plus n pm)))))
    )

; current working mult:
#;(define (mult (m : Nat) (n : Nat))
  (match m #:return Nat
    [z z]
    [(s x)
     (plus n (mult x n))]))

;; mult as a macro and define-red
; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑
#;(define-red eval-mult
  [(#%plain-app ~z n) ~> z]
  [(#%plain-app (~s x) n) ~> (plus n (mult x n))])

#;(define-syntax eval-mult
  (syntax-parser
    [(_ ~z _) #'z]
    [(_ (~s x) n) #'(plus n (mult x n))]
    [debug #:do[(printf "mult: ~a\n" (syntax->datum #'debug))] #:when #f #'debug]
    [(_ n1 n2) #`(#,(mk-reflected #'eval-mult) n1 n2)]))
    
#;(define-typed-syntax mult
  [(_ n1 n2) ≫
   [⊢ n1 ≫ n1- ⇐ Nat]
   [⊢ n2 ≫ n2- ⇐ Nat]
   ------------------
   [⊢ (eval-mult n1- n2-) ⇒ Nat]])

(define/rec/match mult : Nat [n : Nat] -> Nat
  [z => z]
  [(s x) => (plus n (mult x n))])

;; current working exp
#;(define (exp (m : Nat) (e : Nat))
  (match m #:return Nat
    [z (s z)]
    [(s x)
     (mult e (exp x e))]))

;; exponent is first
#;(define-red eval-exp
  [(#%plain-app ~z _) ~> (s z)]
  [(#%plain-app (~s x) e) ~> (mult e (exp x e))])

#;(define-typed-syntax exp
  [(_ n1 n2) ≫
   [⊢ n1 ≫ n1- ⇐ Nat]
   [⊢ n2 ≫ n2- ⇐ Nat]
   ------------------
   [⊢ (eval-exp n1- n2-) ⇒ Nat]])
(define/rec/match exp : [e : Nat] Nat -> Nat
  [z => (s z)]
  [(s x) => (mult e (exp e x))])

(define (square [n : Nat]) (exp n (s (s z))))

#;(define-red eval-zero?
  ;; TODO: this ~z triggers nonid case bc it gets moved to "head" in define-red, in eval.rkt
  ;; but expected the id patexpander case to be triggered
  [(#%plain-app (~z)) ~> true]
  [(#%plain-app (~s x)) ~> false])
#;(define-typed-syntax zero?
  [(_ n) ≫
   [⊢ n ≫ n- ⇐ Nat]
   ------------------
   [⊢ (eval-zero? n-) ⇒ Bool]]
  [:id ≫
   -----
   [≻ (λ [m : Nat]
        (match m #:return Bool
         [(z) true]
         [(s n) false]))]])
#;(define (zero? (n : Nat))
  (match n #:return Bool
    [z true]
    [(s n)
     false]))

(define/rec/match zero? : Nat -> Bool
  [z => true]
  [(s _) => false])

;; nat-equal? with explicit elims
#;(define nat-equal?
  (λ [n : Nat]
    (elim-Nat n
     (λ [x : Nat] (-> Nat Bool))
     zero?
     (λ [n-1 : Nat] [ihn : (-> Nat Bool)]
        (λ [m : Nat]
          (elim-Nat m
           (λ [x : Nat] Bool)
           false
           (λ [m-1 : Nat] [ihm : Bool]
              (ihn m-1))))))))

;; current working version
#;(define (nat-equal? (n : Nat))
  (match n #:return (-> Nat Bool)
    [z zero?]
    [(s n-1)
     (λ (m : Nat)
       (match m #:return Bool
         [z false]
         [(s m-1)
          (nat-equal? n-1 m-1)]))]))
;; (define-red eval-nat-equal?
;;   [(#%plain-app (~z) (~z)) ~> true]
;;   [(#%plain-app (~s x) (~z)) ~> false]
;;   [(#%plain-app (~z) (~s x)) ~> false]
;;   [(#%plain-app (~s x) (~s y)) ~> (nat-equal? x y)])

;; (define-typed-syntax nat-equal?
;;   [(_ n1 n2) ≫
;;    [⊢ n1 ≫ n1- ⇐ Nat]
;;    [⊢ n2 ≫ n2- ⇐ Nat]
;;    ------------------
;;    [⊢ (eval-nat-equal? n1- n2-) ⇒ Bool]]
;;   #;[:id ≫
;;    -----
;;    [≻ (λ [m : Nat]
;;         (match m #:return Bool
;;          [z true]
;;          [(s n) false]))]])

;; nat-equal? with single match,
;; also tests nested match
#;(define/rec/match nat-equal? : Nat [n : Nat] -> Bool
  [z => (match n #:return Bool [z true] [(s x) false])]
  [(s x) => (match n #:return Bool [z false] [(s y) (nat-equal? x y)])])

;; nat-equal? with multi match
(define/rec/match nat-equal? : Nat Nat -> Bool
  [z z => true]
  [z (s _) => false]
  [(s _) z => false]
  [(s x) (s y) =>  (nat-equal? x y)])

;; ;; TODO: some notes for improving nat-equal?-like fns
;; ;; match currently elaborates to elim, which only recurs on one arg,
;; ;; so fns like nat-equal? require explicit currying
;; ;; TODO: automatically do this currying?
;; ;; eg, programmer writes
;; ;; ideally:
;; #;(define (nat-equal? [n : Nat] [m : Nat])
;;   (match (n,m)
;;     [(z,z) true]
;;     [(s n-1),(s m-1) (nat-equal? n-1 m-1)]))
;; ;; somewhat more realistic (currently not working, 2018-09-14)
;; #;(define (nat-equal? [n : Nat] [m : Nat])
;;   (match n #:return Bool
;;     [z
;;      (match m #:return Bool
;;       [z true]
;;       [(s m-1) false])]
;;     [(s n-1)
;;      (match m #:return Bool
;;       [z false]
;;       [(s m-1) (nat-equal? n-1 m-1)])]))      
;; ;; concretely, match (and define) must push the curried λ into the match bodies?
;; ;; eg the fn, which is equiv to (currently inf looping, 2018-09-14, bc recur not inserted for id defs)
;; #;(define nat-equal?
;;   (λ [n : Nat]
;;     (λ [m : Nat]
;;       (match n #:return Bool
;;        [z
;;         (match m #:return Bool
;;          [z true]
;;          [(s m-1) false])]
;;        [(s n-1)
;;         (match m #:return Bool
;;          [z false]
;;          [(s m-1) (nat-equal? n-1 m-1)])]))))
;; ;;(currently inf looping, 2018-09-14, bc recur not inserted for id defs)
;; #;(define nat-equal?
;;   (λ [n : Nat]
;;       (match n #:return (-> Nat Bool)
;;        [z
;;         (λ [m : Nat]
;;           (match m #:return Bool
;;            [z true]
;;            [(s m-1) false]))]
;;        [(s n-1)
;;         (λ [m : Nat]
;;           (match m #:return Bool
;;            [z false]
;;            [(s m-1) (nat-equal? n-1 m-1)]))])))
;; ;; not inf looping, but still broken version
;; #;(define (nat-equal? [n : Nat])
;;   (λ [m : Nat]
;;     (match n #:return Bool
;;      [z
;;       (match m #:return Bool
;;        [z true]
;;        [(s m-1) false])]
;;      [(s n-1)
;;       (match m #:return Bool
;;        [z false]
;;        [(s m-1) (nat-equal? n-1 m-1)])])))


#;(define (even? (n : Nat))
  (match n #:return Bool
    [z true]
    [(s n-1)
     (not (even? n-1))]))

(define/rec/match even? : Nat -> Bool
  [z => true]
  [(s n-1) => (not (even? n-1))])

#;(define (odd? (n : Nat))
  (not (even? n)))

(define/rec/match <= : Nat Nat -> Bool
  [z _ => true]
  [(s n*) z => false]
  [(s n*) (s m*) => (<= n* m*)])
