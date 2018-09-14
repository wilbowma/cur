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

(define (nat-equal? (n : Nat))
  (match n #:return (-> Nat Bool)
    [z zero?]
    [(s n-1)
     (λ (m : Nat)
       (match m #:return Bool
         [z false]
         [(s m-1)
          (nat-equal? n-1 m-1)]))]))

(define (even? (n : Nat))
  (match n #:return Bool
    [z true]
    [(s n-1)
     (not (even? n-1))]))

(define (odd? (n : Nat))
  (not (even? n)))
