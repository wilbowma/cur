#lang cur
(require
 cur/stdlib/bool
 cur/stdlib/nat
 cur/stdlib/sugar)

;; Write dependently-typed code
(if true
    false
    true)

(: + (-> Nat Nat Nat))
(define + plus)
(+ z (s z))

;; Write some macros and Racket meta-programs over dependently-typed code
(begin-for-syntax
  (require
   (only-in racket/base [sub1 r:sub1]))
  (define (nat->unary n)
    (if (zero? n)
        #`z
        #`(s #,(nat->unary (r:sub1 n))))))

(define-syntax (define-numbers syn)
  (syntax-case syn ()
    [(_)
     #`(begin
         #,@(for/list ([i (in-range 10)])
              #`(define #,(format-id syn "Nat-~a" i) #,(nat->unary i))))]))

(define-numbers)
;; (define-numbers) generates the following definitions at macro-expansion time:
#|
 |  (define Nat-0 z)
 |  (define Nat-1 (s z))
 |  (define Nat-2 (s (s z)))
 |  (define Nat-3 (s (s (s z))))
 |  (define Nat-4 (s (s (s (s z)))))
 |  (define Nat-5 (s (s (s (s (s z))))))
 |  (define Nat-6 (s (s (s (s (s (s z)))))))
 |  (define Nat-7 (s (s (s (s (s (s (s z))))))))
 |  (define Nat-8 (s (s (s (s (s (s (s (s z)))))))))
 |  (define Nat-9 (s (s (s (s (s (s (s (s (s z))))))))))
 |  (define Nat-10 (s (s (s (s (s (s (s (s (s (s z)))))))))))
 |#

Nat-0
Nat-5

;; Of course, you could just define #%datum to do the right thing:
(require (only-in cur [#%datum old-datum]))
(define-syntax (#%datum syn)
  (syntax-parse syn
    [(_ . x:nat)
     (nat->unary (syntax->datum #'x))]
    [(_ . e)
     #`(old-datum e)]))

0
5
