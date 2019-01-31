#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

(data bool : 0 Type
      (true : bool)
      (false : bool))

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : -> Type
  [nil* : (list X)]
  [cons* : X (list X) -> (list X)])

(define-implicit nil = nil* 1)
(define-implicit cons = cons* 1 _ inf)
(define-datatype prod [X : Type] [Y : Type] : -> Type
  [pair* : X Y -> (prod X Y)])

(define-implicit pair = pair* 2)

(define/rec/match fst* : [X : Type] [Y : Type] (prod X Y) -> X
  [(pair* _ _  x _) => x])
(define/rec/match snd* : [X : Type] [Y : Type] (prod X Y) -> Y
  [(pair* _ _ _ y) => y])

(define-implicit fst = fst* 2)
(define-implicit snd = snd* 2)

(define/rec/match combine_ : [X : Type] [Y : Type] (list X) (list Y) -> (list (prod X Y))
  [(nil* _) _ => (nil* (prod X Y))]
  [_ (nil* _) => (nil* (prod X Y))]
  [(cons* _ x tx) (cons* _ y ty) => (cons (pair x y) (combine_ X Y tx ty))])

(check-type combine_
  : (∀ [X : Type] [Y : Type] (-> (list X) (list Y) (list (prod X Y)))))

(define-implicit combine = combine_ 2)

(check-type
 (combine (cons 1 (cons 2 nil))
          (cons false (cons false (cons true (cons true nil)))))
 : (list (prod nat bool))
 -> (cons (pair 1 false) (cons (pair 2 false) nil)))
