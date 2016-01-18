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
  (term (e)   ::= x v (app e e) (lambda (x : A) e) (cons e e)
                  (let (x x) = e in e)))

;; TODO: Abstract this over stlc-type, and provide from in OLL
(data Gamma : Type
  (emp-gamma : Gamma)
  (extend-gamma : (-> Gamma Var stlc-type Gamma)))

(define (lookup-gamma (g : Gamma) (x : Var))
  (case* Gamma Type g () (lambda (g : Gamma) (Maybe stlc-type))
    [emp-gamma (none stlc-type)]
    [(extend-gamma (g1 : Gamma) (v1 : Var) (t1 : stlc-type))
     IH: ((ih-g1 : (Maybe stlc-type)))
     (if (var-equal? v1 x)
         (some stlc-type t1)
         ih-g1)]))

(define-relation (has-type Gamma stlc-term stlc-type)
  #:output-coq "stlc.v"
  #:output-latex "stlc.tex"
  [(g : Gamma)
   ------------------------ T-Unit
   (has-type g (stlc-val-->-stlc-term stlc-unit) stlc-unitty)]

  [(g : Gamma)
   ------------------------ T-True
   (has-type g (stlc-val-->-stlc-term stlc-true) stlc-boolty)]

  [(g : Gamma)
   ------------------------ T-False
   (has-type g (stlc-val-->-stlc-term stlc-false) stlc-boolty)]

  [(g : Gamma) (x : Var) (t : stlc-type)
   (== (Maybe stlc-type) (lookup-gamma g x) (some stlc-type t))
   ------------------------ T-Var
   (has-type g (Var-->-stlc-term x) t)]

  [(g : Gamma) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
   (has-type g e1 t1)
   (has-type g e2 t2)
   ---------------------- T-Pair
   (has-type g (stlc-cons e1 e2) (stlc-* t1 t2))]

  [(g : Gamma) (e1 : stlc-term) (e2 : stlc-term)
               (t1 : stlc-type) (t2 : stlc-type)
               (t : stlc-type)
               (x : Var) (y : Var)
   (has-type g e1 (stlc-* t1 t2))
   (has-type (extend-gamma (extend-gamma g x t1) y t2) e2 t)
   ---------------------- T-Let
   (has-type g (stlc-let x y e1 e2) t)]

  [(g : Gamma) (e1 : stlc-term) (t1 : stlc-type) (t2 : stlc-type) (x : Var)
   (has-type (extend-gamma g x t1) e1 t2)
   ---------------------- T-Fun
   (has-type g (stlc-lambda x t1 e1) (stlc--> t1 t2))]

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
  (define index #'z))
(define-syntax (begin-stlc syn)
  (set! index #'z)
  (let stlc ([syn (syntax-case syn () [(_ e) #'e])])
    (syntax-parse syn
      #:datum-literals (lambda : prj * -> quote let in cons bool)
      [(lambda (x : t) e)
       (let ([oldindex index])
         (set! index #`(s #,index))
         ;; Replace x with a de bruijn index, by running a CIC term at
         ;; compile time.
         (normalize/syn
           #`((lambda (x : stlc-term)
                      (stlc-lambda (avar #,oldindex) #,(stlc #'t) #,(stlc #'e)))
             (Var-->-stlc-term (avar #,oldindex)))))]
      [(quote (e1 e2))
       #`(stlc-cons #,(stlc #'e1) #,(stlc #'e2))]
      [(let (x y) = e1 in e2)
       (let* ([y index]
              [x #`(s #,y)])
         (set! index #`(s (s #,index)))
         #`((lambda (x : stlc-term) (y : stlc-term)
              (stlc-let (avar #,x) (avar #,y) #,(stlc #'t) #,(stlc #'e1)
                   #,(stlc #'e2)))
            (Var-->-stlc-term (avar #,x))
            (Var-->-stlc-term (avar #,y))))
       #`(let x  i #,(stlc #'e1))]
      [(e1 e2)
       #`(stlc-app #,(stlc #'e1) #,(stlc #'e2))]
      [() #'(stlc-val-->-stlc-term stlc-unit)]
      [#t #'(stlc-val-->-stlc-term stlc-true)]
      [#f #'(stlc-val-->-stlc-term stlc-false)]
      [(t1 * t2)
       #`(stlc-* #,(stlc #'t1) #,(stlc #'t2))]
      [(t1 -> t2)
       #`(stlc--> #,(stlc #'t1) #,(stlc #'t2))]
      [bool #`stlc-boolty]
      [e
       (if (eq? 1 (syntax->datum #'e))
           #'stlc-unitty
           #'e)])))

(check-equal?
 (begin-stlc (lambda (x : 1) x))
 (stlc-lambda (avar z) stlc-unitty (Var-->-stlc-term (avar z))))
(check-equal?
 (begin-stlc ((lambda (x : 1) x) ()))
 (stlc-app (stlc-lambda (avar z) stlc-unitty (Var-->-stlc-term (avar z)))
           (stlc-val-->-stlc-term stlc-unit)))
(check-equal?
 (begin-stlc '(() ()))
 (stlc-cons (stlc-val-->-stlc-term stlc-unit)
            (stlc-val-->-stlc-term stlc-unit)))
(check-equal?
 (begin-stlc #t)
 (stlc-val-->-stlc-term stlc-true))
