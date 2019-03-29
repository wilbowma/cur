#lang cur
(require cur/stdlib/sugar
         cur/stdlib/equality
         cur/ntac/base
         cur/ntac/standard
         cur/ntac/rewrite
         rackunit/turnstile
         "../rackunit-ntac.rkt")

;; part 2 of 3 of Software Foundations Poly.v chapter

(data bool : 0 Type
      (true : bool)
      (false : bool))

(data nat : 0 Type
      (O : nat) ; letter capital "O"
      (S : (-> nat nat)))

(define/rec/match beq-nat : nat nat -> bool
  [O O => true]
  [O (S _) => false]
  [(S _) O => false]
  [(S n*) (S m*) => (beq-nat n* m*)])

(define/rec/match pred : nat -> nat
  [O => O]
  [(S n-1) => n-1])

;; re-define #%datum to use the new `nat`
(define-syntax #%datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'O]
    [(_ . n:exact-nonnegative-integer)
     #`(S (#%datum . #,(- (syntax-e #'n) 1)))]))

;; * = "full" version; as opposed to hidden-arg version
(define-datatype list [X : Type] : Type
  [nil*]
  [cons* X (list X)])

(define-implicit nil = nil* 1)
(define-implicit :: = cons* 1 _ inf)

(define-syntax lst
  (syntax-parser
    [(_) #'nil]
    [(_ x . rst) #'(:: x (lst . rst))]))

(define/rec/match app_ : [X : Type] (list X) (list X) -> (list X)
  [nil l2 => l2]
  [(:: h t) l2 => (:: h (app_ X t l2))])

(define-implicit app = app_ 1)

(define/rec/match rev_ : [X : Type] (list X) -> (list X)
  [nil => nil]
  [(:: h t) => (app (rev_ X t) (:: h nil))])

(define-implicit rev = rev_ 1)

;; pairs --------------------

(define-datatype prod [X : Type] [Y : Type] : Type
  [pair* X Y])

(define-implicit pair = pair* 2)

(define/rec/match fst* : [X : Type] [Y : Type] (prod X Y) -> X
  [(pair x _) => x])
(define/rec/match snd* : [X : Type] [Y : Type] (prod X Y) -> Y
  [(pair _ y) => y])

(define-implicit fst = fst* 2)
(define-implicit snd = snd* 2)

(define/rec/match combine_ : [X : Type] [Y : Type] (list X) (list Y)
  -> (list (prod X Y))
  [nil _ => (nil* (prod X Y))]
  [_ nil => (nil* (prod X Y))]
  [(:: x tx) (:: y ty) => (:: (pair x y) (combine_ X Y tx ty))])

(check-type combine_
  : (∀ [X : Type] [Y : Type] (-> (list X) (list Y) (list (prod X Y)))))

(define-implicit combine = combine_ 2)

(check-type
 (combine (lst 1 2)
          (lst false false true true))
 : (list (prod nat bool))
 -> (lst (pair 1 false) (pair 2 false)))

(define/rec/match split_ : [X : Type] [Y : Type] (list (prod X Y))
  -> (prod (list X) (list Y))
  [nil => (pair (nil* X) (nil* Y))]
  [(:: (pair m n) xs)
   => (pair (:: m (fst (split_ X Y xs)))
            (:: n (snd (split_ X Y xs))))])

(check-type split_
  : (Π [X : Type] [Y : Type] (-> (list (prod X Y))
                                 (prod (list X) (list Y)))))

(define-implicit split = split_ 2)

(check-type
 (split (lst (pair 1 false) (pair 2 false)))
 : (prod (list nat) (list bool))
 -> (pair (lst 1 2)
          (lst false false)))

(define-datatype option [X : Type] : Type
  [Some* X]
  [None*])

(define-implicit Some = Some* 1)
(define-implicit None = None* 1)

(define-typed-syntax (if tst e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ]
  [⊢ e2 ≫ e2- ⇐ τ]
  ----------
  [≻ (match tst #:return τ [true e1-] [false e2-])])

(define/rec/match nth/error_ : [X : Type] [n : nat] (list X) -> (option X)
  [nil => None]
  [(:: a xs) => (if (beq-nat n 0) (Some a) (nth/error_ X (pred n) xs))])

(define-implicit nth/error = nth/error_ 1)

(check-type (nth/error 0 (lst 4 5 6 7)) : (option nat) -> (Some 4))
(check-type (nth/error 1 (lst (lst 1) (lst 2)))
            : (option (list nat)) -> (Some (lst 2)))
(check-type (nth/error 2 (lst true)) : (option bool) -> None)

(define/rec/match hd/error_ : [X : Type] (list X) -> (option X)
  [nil => None]
  [(:: h _) => (Some h)])

(define-implicit hd/error = hd/error_ 1)

(check-type (hd/error (lst 1 2)) : (option nat) -> (Some 1))
(check-type (hd/error (lst (lst 1) (lst 2)))
            : (option (list nat)) -> (Some (lst 1)))
(check-type (hd/error (nil* nat)) : (option nat) -> None)

(define (do3times_ [X : Type] [f : (-> X X)] [n : X])
  (f (f (f n))))

(define-implicit do3times = do3times_ 1)

(define/rec/match minustwo : nat -> nat
  [O => O]
  [(S O) => O]
  [(S (S n-1)) => n-1])

(check-type (minustwo 4) : nat -> 2)
(check-type (minustwo 3) : nat -> 1)
(check-type (minustwo 2) : nat -> 0)
(check-type (minustwo 1) : nat -> 0)
(check-type (minustwo 0) : nat -> 0)

(check-type (do3times minustwo 9) : nat -> 3)

(define/rec/match negb : bool -> bool
  [true => false]
  [false => true])

(check-type (do3times negb true) : bool -> false)

(define/rec/match filter_ : [X : Type] [p? : (-> X bool)] (list X) -> (list X)
  [nil => nil]
  [(:: h t) => (if (p? h) (:: h (filter_ X p? t)) (filter_ X p? t))])

(define-implicit filter = filter_ 1)

(define/rec/match evenb : nat -> bool
  [O => true]
  [(S O) => false]
  [(S (S n-1)) => (evenb n-1)])


(check-type (filter evenb [lst 1 2 3 4]) : (list nat) -> [lst 2 4])

(define/rec/match length_ : [X : Type] (list X) -> nat
  [nil => 0]
  [(:: h t) => (S (length_ X t))])

(define-implicit length = length_ 1)

(define (length=1?_ {X : Type} [l : (list X)])
  (beq-nat (length l) 1))

(define-implicit length=1? = length=1?_ 1)

;; TODO: unify polymorphic and concrete fn args
(check-type
 (filter (length=1?_ nat) [lst [lst 1 2] [lst 3] [lst 4] [lst 5 6 7] (nil* nat) [lst 8]])
 : (list (list nat))
 -> [lst [lst 3] [lst 4] [lst 8]])

(define (oddb [n : nat]) (negb (evenb n)))

(define (countoddmembers (l : (list nat)))
  (length (filter oddb l)))

(check-type (countoddmembers [lst 1 0 3 1 4 5]) : nat -> 4)
(check-type (countoddmembers [lst 0 2 4]) : nat -> 0)
(check-type (countoddmembers (nil* nat)) : nat -> 0)

(define/rec/match plus : nat [m : nat] -> nat
  [O => m]
  [(S n-1) => (S (plus n-1 m))])

(define/rec/match mult : nat [m : nat] -> nat
  [O => O]
  [(S n-1) => (plus m (mult n-1 m))])

(check-type (do3times (λ [n : nat] (mult n n)) 2) : nat -> 256)

(define (partition_ {X : Type} (test : (-> X bool)) (l : (list X)))
  (pair (filter test l) (filter (λ [n : X] (negb (test n))) l)))

(define-implicit partition = partition_ 1)

(check-type (partition oddb [lst 1 2 3 4 5])
            : (prod (list nat) (list nat)) -> (pair [lst 1 3 5] [lst 2 4]))
(check-type (partition (λ [x : nat] false) [lst 5 9 0])
            : (prod (list nat) (list nat)) -> (pair (nil* nat) [lst 5 9 0]))
(define-theorem partition-test2
  (== (partition (λ [x : nat] false) [lst 5 9 0])
      (pair (nil* nat) [lst 5 9 0]))
  reflexivity)

(define/rec/match map_ : {X : Type} {Y : Type} (f : (-> X Y)) (list X) -> (list Y)
  [nil => nil]
  [(:: h t) => (:: (f h) (map_ X Y f t))])

(define-implicit map = map_ 2)

(check-type
 (map (λ [x : nat] (plus 3 x)) [lst 2 0 2])
 : (list nat) -> [lst 5 3 5])

(define-theorem test-map1
  (== (map (λ [x : nat] (plus 3 x)) [lst 2 0 2]) [lst 5 3 5])
  reflexivity)

(define-theorem test-map2
  (== (map oddb [lst 2 1 2 5]) [lst false true false true])
  reflexivity)

(define-theorem test-map3
  (== (map (λ [n : nat] [lst (evenb n) (oddb n)]) [lst 2 1 2 5])
      [lst [lst true false] [lst false true] [lst true false] [lst false true]])
  reflexivity)

;; these `map` examples additionally test unification of binding types
(define-theorem app-map
  (∀ [X : Type] [Y : Type] [f : (-> X Y)] [l : (list X)] [x : X]
     (== (app (map f l) [lst (f x)])
         (map f (app l [lst x]))))
  by-intros
  (by-induction l #:as [() (y ys IH)]) ; dont shadow previous x
  reflexivity ; 1
  (by-rewrite  IH) ; 2
  reflexivity)

(define-theorem map-rev
  (∀ [X : Type] [Y : Type] [f : (-> X Y)] [l : (list X)]
     (== (map f (rev l))
         (rev (map f l))))
     by-intros
     (by-induction l #:as [() (x xs IH)])
     reflexivity ; 1
     (by-rewriteL IH) ; 2
     (by-rewrite app-map)
     reflexivity)

(define/rec/match flat-map_ : [X : Type] [Y : Type] [f : (-> X (list Y))] (list X)
  -> (list Y)
  [nil => nil]
  [(:: x xs) => (app (f x) (flat-map_ X Y f xs))])

(define-implicit flat-map = flat-map_ 2)

(define-theorem flat-map-test1
  (== (flat-map (λ [n : nat] (lst n n n)) (lst 1 5 4))
      (lst 1 1 1 5 5 5 4 4 4))
  reflexivity)

(define/rec/match option-map_ : [X : Type] [Y : Type] [f : (-> X Y)] (option X)
  -> (option Y)
  [None => None]
  [(Some x) => (Some (f x))])

(define-implicit option-map = option-map_ 2)

(define/rec/match fold_ : [X : Type] [Y : Type] [f : (-> X Y Y)] [b : Y] (list X)
  -> Y
  [nil => b]
  [(:: h t) => (f h (fold_ X Y f b t))])

(define-implicit fold = fold_ 2 inf _ _)

(check-type (fold plus 0 (lst 1 2 3 4)) : nat -> 10)

(define/rec/match andb : bool [b : bool] -> bool
  [true => b]
  [false => false])

;; test partial #%app
;; explicit case
(check-type (fold_ bool bool andb) : (-> bool (list bool) bool))

;; with define-implicit form
(check-type (fold andb) : (-> bool (list bool) bool))

(define-theorem fold-example1
  (== (fold mult 1 (lst 1 2 3 4)) 24)
  reflexivity)

(define-theorem fold-example2
  (== (fold andb true (lst true true false true)) false)
  reflexivity)

;; polymorphic fn
(define-theorem fold-example3
  (== (fold (app_ nat) (nil* nat) (lst (lst 1) (nil* nat) (lst 2 3) (lst 4)))
      (lst 1 2 3 4))
  reflexivity)

(define (flat-map2 [X : Type] [l : (list (list X))])
  (fold (app_ X) (nil* X) l))

(define (constfun_ [X : Type] [x : X])
  (λ [k : nat] x))

(define-implicit constfun = constfun_ 1)

(define ftrue (constfun true))

(define-theorem constfun-example1
  (== (ftrue 0) true)
  reflexivity)

(define-theorem constfun-example2
  (== ((constfun 5) 99) 5)
  reflexivity)

(check-type plus : (-> nat nat nat))

(define plus3 (plus 3))
(check-type plus3 : (-> nat nat))

(define-theorem plus3-test1 (== (plus3 4) 7) reflexivity)
(define-theorem plus3-test2 (== (do3times plus3 0) 9) reflexivity)
(define-theorem plus3-test3 (== (do3times (plus 3) 0) 9) reflexivity)

(define (fold-length_ [X : Type] [l : (list X)])
  (fold (λ [x : X] [n : nat] (S n)) 0 l))

(define-implicit fold-length = fold-length_ 1)

(define-theorem fold-length-test1
  (== (fold-length [lst 4 7 0]) 3)
  reflexivity)

;; this test checks `unexpand` of HO fn
(define-theorem fold-length-correct
  (∀ [X : Type] [l : (list X)]
     (== (fold-length l) (length l)))
  (by-intros X l)
  (by-induction l #:as [() (x xs IH)])
  reflexivity     ; 1
  (by-rewriteL IH) ; 2
  reflexivity)

(check-type fold-length-correct
            : (∀ [X : Type] [l : (list X)]
                 (== (fold-length l) (length l))))

(define (fold-map_ [X : Type] [Y : Type] [f : (-> X Y)] [l : (list X)])
  (fold (λ x l1 (:: (f x) l1)) (nil* Y) l))

(define-implicit fold-map = fold-map_ 2)

(define-theorem fold-map-correct
  (∀ [X : Type] [Y : Type] [f : (-> X Y)] [l : (list X)]
     (== (map f l) (fold-map f l)))
  (by-intros X Y f l)
  (by-induction l #:as [() (x xs IH)])
  reflexivity ;1
  (by-rewrite IH)
  reflexivity)

(define (prod-curry_ [X : Type] [Y : Type] [Z : Type]
                     [f : (-> (prod X Y) Z)] [x : X] [y : Y])
  (f (pair x y)))

(define (prod-uncurry_ [X : Type] [Y : Type] [Z : Type]
                       [f : (-> X Y Z)] [p : (prod X Y)])
  (f (fst p) (snd p)))

(define-implicit prod-curry = prod-curry_ 3)
(define-implicit prod-uncurry = prod-uncurry_ 3)

(define-theorem map-test2
  (== (map (λ [x : nat] (plus 3 x)) [lst 2 0 2]) (lst 5 3 5))
  reflexivity)

(define-theorem uncurry-curry
  (∀ [X : Type] [Y : Type] [Z : Type]
     [f : (-> X Y Z)] [x : X][y : Y]
     (== (prod-curry (prod-uncurry f) x y) (f x y)))
  by-intros
  reflexivity)

;; tests destruct and match with polymorphic type
(define-theorem curry-uncurry
  (∀ [X : Type] [Y : Type] [Z : Type]
     [f : (-> (prod X Y) Z)] [p : (prod X Y)]
     (== (prod-uncurry (prod-curry f) p) (f p)))
  (by-intros X Y Z f p)
  (by-destruct p #:as [(x y)])
  reflexivity)

; nth/error-informal
#;(∀ [X : type] [n : nat] [l : (list X)]
   (-> (== (length l) n)
       (== (nth/error n l) (None* nat))))
