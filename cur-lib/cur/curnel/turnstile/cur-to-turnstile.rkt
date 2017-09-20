#lang racket
(require
 racket/require-syntax
 racket/provide-syntax
 (for-syntax
  ;; imported for export
  (except-in racket import export)
  racket/syntax
  syntax/parse
  ;racket/require-transform
  racket/provide-transform
  "stxutils.rkt"
  "runtime-utils.rkt")

  (rename-in turnstile/examples/dep-ind
             [Type dep-Type]
             [* dep-*]
             [ Π dep-Π]
             [→ dep-→]
             [∀ dep-∀]
         [= dep-=]
         [eq-refl dep-eq-refl]
         [eq-elim dep-eq-elim]
         [λ dep-λ]
         [#%app dep-#%app]
         [ann dep-ann]
         [define-datatype dep-define-datatype]
         [define dep-define]
         [define-type-alias dep-define-type-alias])
  
  "reflection.rkt")
; )
(provide
 turn-Type
 turn-define
 turn-λ
; turn-Π
 turn-app
; turn-axiom
; turn-data
; turn-new-elim
; turn-elim
; turn-void
  #;[cur-require require]
  
  (rename-out [cur-provide turn-provide]
  )
 ;provide-with-types
  )


(define-syntax (turn-Type syn)
   (syntax-parse syn                 
    [(_ i:exact-nonnegative-integer)
     #'(dep-Type i)]

     ;;where/how to add a helpful error?  right now it's "expected exact-nonnegative-integer"
     #;[_ (raise-syntax-error
     'core-type-error
     "helpful Type error here")]
     ))

(define-syntax (turn-define syn)
  (syntax-parse syn
    [(_:top-level-id name:id body:expr)
     #'(dep-define name body)]))


(define-syntax (turn-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) e:expr)
     ;;used to be t1:cur-kind
     #'(dep-λ ([x : t1]) e)]))


#;(define-syntax (turn-Π syn)
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:with (~var _ (cur-kind/ctx (list (cons #'x #'t1.reified)))) #'e.reified
     #'(dep-Π ([x:id : t1] ...) τ_out)])

(define-syntax (turn-app syn)
  (syntax-parse syn
    [(_ e1:expr e2:expr ...)
      #'(dep-#%app e1 e2 ...)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;
 (define-syntax (turn-axiom syn)
   syn)
 
 (define-syntax (turn-data syn)
   syn)
 
 (define-syntax (turn-new-elim syn)
   syn)
 

 (define-syntax (turn-void syn)
   syn)



(module+ test
  (require
   chk
   (only-in (submod "..")
            [turn-Type Type]
            [turn-define define]
            [turn-λ λ]
;            [turn-Π Π]
            [turn-app #%app]
;            [turn-axiom axiom]
;            [turn-data data]
#;            [turn-new-elim elim]))


  ;;; defines don't work in chk, here are some defines to comment/uncomment

  ;;;;;;;;;define should succeed;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define x (Type 1)) ;OK

  (define kittens (Type 3)) ;OK

  (define id (λ (x : (Type 2)) x)) ;OK 

  (define id2 (λ (A : (Type 3)) (λ (a : A) a))) ;OK? (is this supposed to work?  it does.  came from original tests)

    ;;;;;;;;;define should fail;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; "unexpected term z at..." OK
;;;   (define y (define z (Type 1)) z)

;;; "unexpected term z at..." OK
;;;   (define y (define z (Type 1) x) z)

;;;"invalid syntax Type" OK
;;;   (define x Type)

;;;"unexpected term..." OK
;;;   (define x (Type 1) (Type 1))

  
  (chk
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Type should succeed;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;note: x here previously defined as (Type 1)
   #:t x ;OK
   
   #:t (Type 1) ;OK

   #:t (Type 3) ;OK

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Type should fail;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    
;;   #:x #rx""expected universe level but found|unbound identifier z" ;;TODO currently gives Racket type error for z, do better?
;;  (Type z) ;OK

  

;;;;;;;;;;;;;;;;;;;; λ should succeed ;;;;;;;;;;;;;;;;;;;;

;;;   #:t (λ (y : x) x) ;FIXME #%datum error, unusable
;;;;;;;;;;;;;;;;;;;; λ should fail;;;;;;;;;;;;;;;;;;;;

 ;;;(mine) (note: should fail b/c id is a λ, not a type)
;;;#x #rx"Expected type"   
;;;(λ (x : id) x)

;;;;;;;;;;;;;;;;;;;; app should succeed;;;;;;;;;;;;;;;
#:t ((λ (x : (Type 2)) x) (Type 1)) ;OK

;;;;;;;;;;;;;;;;;;;; app should fail;;;;;;;;;;;;;;;;;;;

;;;#:x #rx"type mismatch" ;;TODO rewrite this test it matches, but does fail!
;;;((λ (x : (Type 2)) x) (Type 3)) ;OK

;;;(mine) (note: should fail because id is (Type 2)→(Type 2), kittens is (Type 3)
;;;#x #rx"type mismatch" ;;TODO same as above    
;;;(id kittens) ;OK
)
;------------------------------------------------------------------------------------------;
;------------------------------- Below: not implemented yet -------------------------------;
#;(chk
;;;;;;;;;;;;;;;;;;;; Π should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;
   #:t (Π (x : (Type 1)) (Type 1))
   #:t (Π (x : (Type 1)) (Type 2))


   
;;;;;;;;;;;;;;;;;;;; Π should fail ;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;   #:x #rx"expected function but found x"
;;;   (Π (x : (x (Type 1))) (Type 1))

;;;   #:x #rx"expected function but found x"
;;;   (Π (x : (Type 1)) (x (Type 1)))

;;;   #:x #rx"expected function but found x"
;;;   (Π (y : (Type 1)) (x (Type 1)))

;;;   #:x #rx"expected a kind (a term whose type is a universe) but found a term of type (Π (x : (Type 0)) (Type 0))"
;;;   (Π (y : (λ (x : (Type 0)) x)) (x (Type 1)))

  )
#;(chk
;;;;;;;;;;;;;;;;;;;; axiom should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;; axiom should fail ;;;;;;;;;;;;;;;;;;;;;;;;;   
   )
#;(chk
;;;;;;;;;;;;;;;;;;;; data should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;; data should fail ;;;;;;;;;;;;;;;;;;;;;;;;;   
   )
  #;(chk

;;;;;;;;;;;;;;;;;;;; elim should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;; elim should fail ;;;;;;;;;;;;;;;;;;;;;;;;;   

     )
)






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;original tests;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#;(module+ test
;; Should fail with good error, do (TODO Ish. Error messages still need polish)

((λ (x : (Type 2)) x) (Type 1))  

;; Should fail with good error, do (ish; see above)
;((λ (x : (Type 2)) x) (Type 2))
;((Type 1) (Type 2))

(id (Type 1))

(define id2 (λ (A : (Type 3)) (λ (a : A) a)))
((id2 (Type 2)) (Type 1))

; Should fail with good error, does
;((id2 (Type 2)) (Type 2))

(((λ (Nat : (Type 3))
     (λ (z : Nat)
       (λ (s : (Π (n : Nat) Nat))
         z)))
  (Type 2))
 (Type 1))

(axiom Nat : (Type 0))
(axiom z : Nat)
(axiom s : (Π (y : Nat) Nat))
(axiom meow : (Π (x : (Type 1)) (Type 0)))

;; should fail with good error, does
;(axiom meow2 : ((Type 1) (Type 2)))

;; should fail, does
;(axiom meow3 : (λ (x : (Type 0)) x))

; Should fail with good error, does
;(define y (axiom Nat : (Type 0)))

z
; should fail with good error, does
;(z (Type 0))
(meow (Type 0))
; Should fail with good error, does
;(meow 1)
meow

(axiom Vec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0))))
(axiom nil : (Π (A : (Type 0)) ((Vec A) z)))
(nil Nat)
;
((λ (a : ((Vec Nat) z)) z) (nil Nat))
(axiom NotVec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0))))
;; Should fail, does
;;((λ (a : ((NotVec Nat) z)) z) (nil Nat))
;
(define test1 (λ (a : (Π (x : Nat) Nat)) (a z)))
s
; should fail; does, with good error
;(test1 z)
(test1 s)

; TODO this is bad:
; (require racket/base)
; looks like #%app gets redefined by racket/base...
; but this behavior is consistent with typed/racket... redefine require to emit warnings when base
; forms are redefined

;; should fail with good error, does
;(require (only-in racket/base list))
;(meow (list 1))

;; Should fail with good error, does
#;(data Nat : 0 (Type 0)
      (z : Nat)
      (s : (Π (x : Nat) Nat)))

#;(data Nat2 : 0 (Type 0)
      (z : Nat2)
      (s : (Π (x : Nat) Nat)))

;; TODO: goodish error: types need resugaring
#;(data Nat2 : 0 (Type 0)
      (z2 : Nat2)
      (s2 : (Π (x : Nat) Nat)))

;; TODO: Should fail, does but with wrong error.
#;(data Nat2 : 0 (id (Type 1))
      (z2 : Nat2)
      (s2 : (Π (x : Nat) Nat)))

(data Nat2 : 0 (Type 0)
      (z2 : Nat2)
      (s2 : (Π (x : Nat2) Nat2)))

z2

;; should fail with good error, does
#;(new-elim z (λ (x : Nat) Nat)
      (z (λ (n : Nat) n)))

;; TODO Should fail with type error, does, but needs improvement
#;(new-elim z2 (λ (x : Nat2) Nat2)
      (z2 (λ (n : Nat2) n)))

#;(require (only-in racket displayln [#%app unsafe-racket-apply]))
#;(unsafe-racket-apply displayln "mark")
(new-elim (s2 z2) (λ (x : Nat2) Nat2)
      ((s2 z2) (λ (n : Nat2) (λ (IH : Nat2) (s2 IH)))))

;; should fail with good error, does
#;(new-elim (s2 z2) Nat2
      (z2 (λ (n : Nat2) n)))

;; should fail with good error, does
#;(new-elim (s2 z2) (λ (x : Nat2) Nat2)
      (z2))

;; TODO: should fail with good error, doish. needs resugaring/syntax->datum
#;(new-elim (s2 z2) (λ (x : Nat) Nat2)
      (z2))

;; Should fail with good error, does
#;(new-elim (s2 z2) (λ (x : Nat2) (λ (y : Nat) (Type 0)))
      (z2 (λ (x : Nat2) (λ (IH : Nat) IH))))

;; TODO: Should fail with good error, does ish
#;(new-elim (s2 z2) (λ (x : Nat2) Nat)
      (z2 (λ (x : Nat2) (λ (IH : Nat) IH))))

(data Maybe : 1 (Π (A : (Type 0)) (Type 0))
      (none : (Π (A : (Type 0)) (Maybe A)))
      (just : (Π (A : (Type 0)) (Π (a : A) (Maybe A)))))

((just Nat) z)

((λ (f : (Π (A : (Type 0)) (Type 0))) z) Maybe)

(new-elim (none Nat) (λ (x : (Maybe Nat)) Nat)
      (z (λ (a : Nat) a)))

(new-elim ((just Nat) (s z)) (λ (x : (Maybe Nat)) Nat)
      (z (λ (a : Nat) a)))

;; TODO Should fail with type error, does but needs improvement
#;((λ (x : (new-elim z2 (λ (x : Nat2) (Type 1))
               ((Type 0) (λ (x : Nat2) (Type 0))))) x) Nat)

((λ (x : (new-elim (s2 z2) (λ (x : Nat2) (Type 1))
               ((Type 0) (λ (x : Nat2) (λ (IH : (Type 1)) IH))))) x) Nat)
  )

















 ;;;;;;;;;;;;;;;;;;;;;;;;copypasta stuff;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;not sure why this is here;;;
(define-syntax (cur-provide syn)
  (syntax-parse syn
    [(_ spec ...)
     #'(provide (provide-with-types spec) ...)]))

;;;taken from type-check.rkt to maybe throw cur type errors at some point?  

;; TODO: Should be catchable; maybe should have hierarchy. See current Curnel
  ;; TODO: Should be in separate module

  ;; syn: the source syntax of the error
  ;; expected: a format string describing the expected type or term.
  ;; term: a datum or format string describing the term that did not match the expected property. If a
  ;;       format string, remaining args must be given as rest.
  ;; type: a datum or format string describing the type that did not match the expected property. If a
  ;;       format string, remaining args must be given as rest.
  ;; rest: more datums
  (define (cur-type-error syn expected term type . rest)
    (raise-syntax-error
     'core-type-error
     (apply
      format
      (format "Expected ~a, but found ~a of type ~a."
              expected
              term
              type)
      rest)
     syn))

;;;;;;;;;;;;;;;;;for reference, from type-check.rkt;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(define-syntax (typed-Π syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:cur-kind) (~var e (cur-expr/ctx (list (cons #'x #'t1.reified)))))
     #:with (~var _ (cur-kind/ctx (list (cons #'x #'t1.reified)))) #'e.reified
     (make-cur-runtime-pi
      syn
      #'t1.reified
      (syntax-local-identifier-as-binding (syntax-local-introduce #'x))
      (syntax-local-introduce #'e.reified))]))

(define-syntax (typed-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_:definition-id name:id : type:cur-axiom-telescope)
     #:with c (format-id this-syntax "constant:~a" #'name #:source #'name)
     #`(begin
         (struct c constant (#,@(attribute type.name-ls)) #:transparent
;           #:extra-constructor-name name1
           #:reflection-name 'name)
         (define name ((curry c)))
         (define-for-syntax name
           (constant-info #'type.reified #f 0 #f #f #f #f #f #f #f #f)))]))





|#
