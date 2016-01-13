#lang cur
(require
 rackunit
 cur/stdlib/nat
 cur/stdlib/sugar
 cur/olly
 cur/stdlib/maybe
 cur/stdlib/bool
 cur/stdlib/prop)

(define-language stlc
  #:vars (x)
  #:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  (val  (v)   ::= true false unit)
  ;; TODO: Allow datum, like 1, as terminals
  (type (A B) ::= boolty unitty (-> A B) (* A A))
  (term (e)   ::= x v (app e e) (lambda (#:bind x : A) e) (cons e e)
                  (let (#:bind x #:bind x) = e in e)))

;; TODO: Abstract this over stlc-type, and provide from in OLL
(data Gamma : Type
  (emp-gamma : Gamma)
  (extend-gamma : (-> Gamma Var stlc-type Gamma)))

(define (lookup-gamma (g : Gamma) (x : Var))
  (match g
    [emp-gamma (none stlc-type)]
    [(extend-gamma (g1 : Gamma) (v1 : Var) (t1 : stlc-type))
     (if (var-equal? v1 x)
         (some stlc-type t1)
         (recur g1))]))

(define (shift-var (v : Var))
  (match v
    [(avar (n : Nat))
     (avar (s n))]))

(define (shift (g : Gamma))
  (match g
    [emp-gamma emp-gamma]
    [(extend-gamma (g1 : Gamma) (v1 : Var) (t1 : stlc-type))
     (extend-gamma (recur g1) (shift-var v1) t1)]))

(define-relation (has-type Gamma stlc-term stlc-type)
  #:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  [(g : Gamma)
   ------------------------ T-Unit
   (has-type g (stlc-val->stlc-term stlc-unit) stlc-unitty)]

  [(g : Gamma)
   ------------------------ T-True
   (has-type g (stlc-val->stlc-term stlc-true) stlc-boolty)]

  [(g : Gamma)
   ------------------------ T-False
   (has-type g (stlc-val->stlc-term stlc-false) stlc-boolty)]

  [(g : Gamma) (x : Var) (t : stlc-type)
   (== (Maybe stlc-type) (lookup-gamma g x) (some stlc-type t))
   ------------------------ T-Var
   (has-type g (Var->stlc-term x) t)]

  [(g : Gamma) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
   (has-type g e1 t1)
   (has-type g e2 t2)
   ---------------------- T-Pair
   (has-type g (stlc-cons e1 e2) (stlc-* t1 t2))]

  [(g : Gamma) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
               (t : stlc-type)
   (has-type g e1 (stlc-* t1 t2))
   (has-type (extend-gamma (extend-gamma (shift (shift g)) (avar z) t1) (avar (s z)) t2) e2 t)
   ---------------------- T-Let
   (has-type g (stlc-let e1 e2) t)]

  [(g : Gamma) (e1 : stlc-term) (t1 : stlc-type) (t2 : stlc-type)
   (has-type (extend-gamma (shift g) (avar z) t1) e1 t2)
   ---------------------- T-Fun
   (has-type g (stlc-lambda t1 e1) (stlc--> t1 t2))]

  [(g : Gamma) (e1 : stlc-term) (e2 : stlc-term)
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
            #`(Var->stlc-term (avar #,x)))]
         [else #'e])])))

(check-equal?
 (begin-stlc (lambda (x : 1) x))
 (stlc-lambda stlc-unitty (Var->stlc-term (avar z))))
(check-equal?
 (begin-stlc ((lambda (x : 1) x) ()))
 (stlc-app (stlc-lambda stlc-unitty (Var->stlc-term (avar z)))
           (stlc-val->stlc-term stlc-unit)))
(check-equal?
 (begin-stlc (lambda (x : 1) (lambda (y : 1) x)))
 (stlc-lambda stlc-unitty (stlc-lambda stlc-unitty (Var->stlc-term (avar (s z))))))
(check-equal?
 (begin-stlc '(() ()))
 (stlc-cons (stlc-val->stlc-term stlc-unit)
            (stlc-val->stlc-term stlc-unit)))
(check-equal?
 (begin-stlc #t)
 (stlc-val->stlc-term stlc-true))
