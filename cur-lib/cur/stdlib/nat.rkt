#lang s-exp "../main.rkt"

;; TODO: override (all-defined-out) to enable exporting these properly.
(provide #%datum Nat
         z s add1 sub1 plus mult exp square zero? nat-equal? even? odd?)

(require "datum.rkt" "sugar.rkt" "bool.rkt")

(define-datatype Nat : Type
  [z : Nat]
  [s : (-> Nat Nat)])

(begin-for-syntax
  (provide nat->unary)
  (define (nat->unary n)
    (if (zero? n)
        #`z
        #`(s #,(nat->unary (sub1 n))))))

(begin-for-syntax
  (provide nat-datum)
  (define (nat-datum syn f)
    (syntax-parse syn
      [x:nat
       (nat->unary (syntax->datum #'x))]
      [_ (f syn)]))
  (current-datum nat-datum))

(define (add1 (n : Nat)) (s n))

(define (sub1 (n : Nat))
  (match n #:return Nat
    [z z]
    [(s x) x]))

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


;; plus, unrolling recursive call
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


(define (plus [n1 : Nat] [n2 : Nat])
  (match n1 #:return Nat
   [z n2]
   [(s x) (s (plus x n2))]))


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

(define (mult (m : Nat) (n : Nat))
  (match m #:return Nat
    [z z]
    [(s x)
     (plus n (mult x n))]))

(define (exp (m : Nat) (e : Nat))
  (match m #:return Nat
    [z (s z)]
    [(s x)
     (mult e (exp x e))]))

;; TODO: dont need run?
;(define square (run (exp (s (s z)))))
(define square (exp (s (s z))))

(define (zero? (n : Nat))
  (match n #:return Bool
    [z true]
    [(s n)
     false]))

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

;; working version
(define (nat-equal? (n : Nat))
  (match n #:return (-> Nat Bool)
    [z zero?]
    [(s n-1)
     (λ (m : Nat)
       (match m #:return Bool
         [z false]
         [(s m-1)
          (nat-equal? n-1 m-1)]))]))
;; TODO: some notes for improving nat-equal?-like fns
;; match currently elaborates to elim, which only recurs on one arg,
;; so fns like nat-equal? require explicit currying
;; TODO: automatically do this currying?
;; eg, programmer writes
;; ideally:
#;(define (nat-equal? [n : Nat] [m : Nat])
  (match (n,m)
    [(z,z) true]
    [(s n-1),(s m-1) (nat-equal? n-1 m-1)]))
;; somewhat more realistic (currently not working, 2018-09-14)
#;(define (nat-equal? [n : Nat] [m : Nat])
  (match n #:return Bool
    [z
     (match m #:return Bool
      [z true]
      [(s m-1) false])]
    [(s n-1)
     (match m #:return Bool
      [z false]
      [(s m-1) (nat-equal? n-1 m-1)])]))      
;; concretely, match (and define) must push the curried λ into the match bodies?
;; eg the fn, which is equiv to (currently inf looping, 2018-09-14, bc recur not inserted for id defs)
#;(define nat-equal?
  (λ [n : Nat]
    (λ [m : Nat]
      (match n #:return Bool
       [z
        (match m #:return Bool
         [z true]
         [(s m-1) false])]
       [(s n-1)
        (match m #:return Bool
         [z false]
         [(s m-1) (nat-equal? n-1 m-1)])]))))
;;(currently inf looping, 2018-09-14, bc recur not inserted for id defs)
#;(define nat-equal?
  (λ [n : Nat]
      (match n #:return (-> Nat Bool)
       [z
        (λ [m : Nat]
          (match m #:return Bool
           [z true]
           [(s m-1) false]))]
       [(s n-1)
        (λ [m : Nat]
          (match m #:return Bool
           [z false]
           [(s m-1) (nat-equal? n-1 m-1)]))])))
;; not inf looping, but still broken version
#;(define (nat-equal? [n : Nat])
  (λ [m : Nat]
    (match n #:return Bool
     [z
      (match m #:return Bool
       [z true]
       [(s m-1) false])]
     [(s n-1)
      (match m #:return Bool
       [z false]
       [(s m-1) (nat-equal? n-1 m-1)])])))


(define (even? (n : Nat))
  (match n #:return Bool
    [z true]
    [(s n-1)
     (not (even? n-1))]))

(define (odd? (n : Nat))
  (not (even? n)))
