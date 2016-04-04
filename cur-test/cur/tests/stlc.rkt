#lang cur
(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/list
 cur/stdlib/sugar
 cur/olly
 cur/stdlib/maybe
 cur/stdlib/bool
 cur/stdlib/prop)

(define-language stlc
  #:vars (x)
  ; TODO BUG: Disabled until #40 fixed.
  ;#:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  (val  (v)   ::= true false unit)
  ;; TODO: Allow datum, like 1, as terminals
  (type (A B) ::= boolty unitty (-> A B) (* A A))
  (term (e)   ::= x v (app e e) (lambda (#:bind x : A) e) (cons e e)
                  (let (#:bind x #:bind x) = e in e)))

(define lookup-env (list-ref stlc-type))

(define (extend-env (g : (List stlc-type)) (t : stlc-type))
  (cons stlc-type t g))

(define-relation (has-type (List stlc-type) stlc-term stlc-type)
  ; TODO BUG: Disabled until #40 fixed.
  ;#:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  [(g : (List stlc-type))
   ------------------------ T-Unit
   (has-type g (stlc-val->stlc-term stlc-unit) stlc-unitty)]

  [(g : (List stlc-type))
   ------------------------ T-True
   (has-type g (stlc-val->stlc-term stlc-true) stlc-boolty)]

  [(g : (List stlc-type))
   ------------------------ T-False
   (has-type g (stlc-val->stlc-term stlc-false) stlc-boolty)]

  [(g : (List stlc-type)) (x : Nat) (t : stlc-type)
   (== (Maybe stlc-type) (run (lookup-env g x)) (some stlc-type t))
   ------------------------ T-Var
   (has-type g (Nat->stlc-term x) t)]

  [(g : (List stlc-type)) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
   (has-type g e1 t1)
   (has-type g e2 t2)
   ---------------------- T-Pair
   (has-type g (stlc-cons e1 e2) (stlc-* t1 t2))]

  [(g : (List stlc-type)) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
               (t : stlc-type)
   (has-type g e1 (stlc-* t1 t2))
   (has-type (run (extend-env (extend-env g t1) t2)) e2 t)
   ---------------------- T-Let
   (has-type g (stlc-let e1 e2) t)]

  [(g : (List stlc-type)) (e1 : stlc-term) (t1 : stlc-type) (t2 : stlc-type)
   (has-type (run (extend-env g t1)) e1 t2)
   ---------------------- T-Fun
   (has-type g (stlc-lambda t1 e1) (stlc--> t1 t2))]

  [(g : (List stlc-type)) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
   (has-type g e1 (stlc--> t1 t2))
   (has-type g e2 t1)
   ---------------------- T-App
   (has-type g (stlc-app e1 e2) t2)])

;; A parser, for a deep-embedding of STLC.
;; TODO: We should be able to generate these
;; TODO: When generating a parser, will need something like (#:name app (e e))
;; so I can name a constructor without screwing with syntax.
(begin-for-syntax
  (define (dict-shift d)
    (for/fold ([d (make-immutable-hash)])
              ([(k v) (in-dict d)])
      (dict-set d k #`(s #,v)))))
(define-syntax (begin-stlc syn)
  (let stlc ([syn (syntax-case syn () [(_ e) #'e])]
             [d (make-immutable-hash)])
    (syntax-parse syn
      #:datum-literals (lambda : prj * -> quote let in cons bool)
      [(lambda (x : t) e)
       #`(stlc-lambda #,(stlc #'t d) #,(stlc #'e (dict-set (dict-shift d) (syntax->datum #'x) #`z)))]
      [(quote (e1 e2))
       #`(stlc-cons #,(stlc #'e1 d) #,(stlc #'e2 d))]
      [(let (x y) = e1 in e2)
       #`(stlc-let #,(stlc #'t d) #,(stlc #'e1 d)
                   #,(stlc #'e2 (dict-set* (dict-shift (dict-shift d))
                                           (syntax->datum #'x) #`z
                                           (syntax->datum #'y) #`(s z))))]
      [(e1 e2)
       #`(stlc-app #,(stlc #'e1 d) #,(stlc #'e2 d))]
      [() #'(stlc-val->stlc-term stlc-unit)]
      [#t #'(stlc-val->stlc-term stlc-true)]
      [#f #'(stlc-val->stlc-term stlc-false)]
      [(t1 * t2)
       #`(stlc-* #,(stlc #'t1 d) #,(stlc #'t2 d))]
      [(t1 -> t2)
       #`(stlc--> #,(stlc #'t1 d) #,(stlc #'t2 d))]
      [bool #`stlc-boolty]
      [e
       (cond
         [(eq? 1 (syntax->datum #'e))
          #'stlc-unitty]
         [(dict-ref d (syntax->datum #'e) #f) =>
          (lambda (x)
            #`(Nat->stlc-term #,x))]
         [else #'e])])))

(check-equal?
 (begin-stlc (lambda (x : 1) x))
 (stlc-lambda stlc-unitty (Nat->stlc-term z)))
(check-equal?
 (begin-stlc ((lambda (x : 1) x) ()))
 (stlc-app (stlc-lambda stlc-unitty (Nat->stlc-term z))
           (stlc-val->stlc-term stlc-unit)))
(check-equal?
 (begin-stlc (lambda (x : 1) (lambda (y : 1) x)))
 (stlc-lambda stlc-unitty (stlc-lambda stlc-unitty (Nat->stlc-term (s z)))))
(check-equal?
 (begin-stlc '(() ()))
 (stlc-cons (stlc-val->stlc-term stlc-unit)
            (stlc-val->stlc-term stlc-unit)))
(check-equal?
 (begin-stlc #t)
 (stlc-val->stlc-term stlc-true))
