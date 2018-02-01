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
  "runtime-utils.rkt"
  syntax/to-string
  )

 (only-in turnstile/lang define- infer)
  (rename-in
   turnstile/examples/dep-ind-cur
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

(begin-for-syntax
  (require (only-in rackunit require/expose))
  (require/expose turnstile/examples/dep-ind-cur (assign-type)))

(provide
 turn-Type
 turn-define
 turn-λ
 turn-Π
 turn-app
 turn-axiom
 turn-data
 turn-new-elim
; turn-elim
; turn-void
  #;[cur-require require]
 ;provide-with-types
  )

(define-syntax (turn-Type syn)
   (syntax-parse syn
    [(_ i:exact-nonnegative-integer)
     (quasisyntax/loc syn (dep-Type i))]))

(define-syntax (turn-define syn)
  (syntax-parse syn
    [(_:top-level-id name:id body:expr)
     (quasisyntax/loc syn (dep-define name body))]))


(define-syntax (turn-λ syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ (x:id : t1:expr) ... e:expr)
     (quasisyntax/loc syn (dep-λ [x : t1] ... e))]))

(define-syntax (turn-Π syn)
    (syntax-parse syn #:datum-literals (:)
    [(_ (x:id : t1:expr) ... e:expr)
     (quasisyntax/loc syn (dep-Π [x : t1] ... e))]))

(define-syntax (turn-app syn)
  (syntax-parse syn
    [(_ e1:expr e2:expr ...)
      (quasisyntax/loc syn (dep-#%app e1 e2 ...))]))


(begin-for-syntax
  (define (parse-telescope-names type)
    (syntax-parse type
      #:datum-literals (:)
      #:literals (turn-Π)
      [(turn-Π (x : t) telescope) (cons (quasisyntax/loc type x) (parse-telescope-names #'telescope))]
      [result '()]))
  (define (parse-telescope-annotations type)
    (syntax-parse type
      #:datum-literals (:)
      #:literals (turn-Π)
      [(turn-Π (x : t) telescope) (cons (quasisyntax/loc type [x : t]) (parse-telescope-annotations #'telescope))]
      [result '()]))
  (define (parse-telescope-result type)
    (syntax-parse type
      #:datum-literals (:)
      #:literals (turn-Π)
      [(turn-Π (x : t) telescope) (parse-telescope-result #'telescope)]
      [result type]))
  )

(define-syntax (turn-data syn)
  (syntax-parse syn #:datum-literals (:)
    [(_ Name:id : p:nat (turn-Π (x : ty) body)
        (c-name:id : c-type) ...)
     #:with type #'(turn-Π (x : ty) body)
     #:with Result (parse-telescope-result (attribute type))
     #:do [(define param-count (syntax->datum #'p))
           (define telescope-anns (parse-telescope-annotations (attribute type)))]
     #:with ([A : AT] ...) (take telescope-anns param-count)
     #:with ([I : IT] ...) (drop telescope-anns param-count)
     #:do [(define c-telescope-anns
             (for/list ([t (attribute c-type)])
               (parse-telescope-annotations t)))]
     #:with (([cA : cAT] ...) ...) (for/list ([as c-telescope-anns])
                                     (take as param-count))
     #:with (([r : rT] ...) ...) (for/list ([as c-telescope-anns])
                                   (drop as param-count))
     #:with (c_result ...) (for/list ([t (attribute c-type)])
                             (parse-telescope-result t))
     (quasisyntax/loc syn
       (dep-define-datatype Name (A : AT) ... : (I : IT) ... -> Result
                            [c-name : (dep-Π [cA : cAT] ...
                                             (dep-Π [r : rT] ...
                                                    c_result))]
                            ...))]
    [(_ Name:id : 0 type ;;per dep-ind-cur-tests, still need special case for (Type 0): must use * or Type?
        (c-name:id : c-type) ...)
     #:with (([r : rT] ...) ...) (for/list ([t (syntax->list #'(c-type ...))])
                                   (parse-telescope-annotations t))
     #:with (c_result ...) (for/list ([t (syntax->list #'(c-type ...))])
                             (parse-telescope-result t))
     (quasisyntax/loc syn
       (dep-define-datatype Name : dep-*
                            [c-name :  (dep-Π [r : rT] ...
                                             c_result)] ...))]))

(define-syntax (turn-new-elim syn)
  (syntax-parse syn
    [(_ target:expr motive:expr (method:expr ...))
     #:with elim-name (syntax-property (first (fourth (infer (list #'target) #:ctx '())))
                                       'elim-name)
     (quasisyntax/loc syn (elim-name target motive method ...))]))


(define-syntax (turn-axiom syn)
  (syntax-parse syn
    #:datum-literals (:)
    [(_ name:id (~datum :) type)
     #:with c (format-id this-syntax "constant:~a" #'name #:source #'name)
     #:with (arg ...) (parse-telescope-names #'type)
     #:with name- (format-id syn "~a-" #'name #:source #'name)
     (quasisyntax/loc syn
       (begin
         (struct c (arg ...) #:transparent #:reflection-name 'name)
         (define name- ((curry c)))
         (define-syntax name
           (make-rename-transformer
            (assign-type #'name- #'#,(local-expand #'type 'expression null))))))]))




;------------------------------------------------------------------------------------------;
;------------------------------- not implemented yet -------------------------------;



 (define-syntax (turn-void syn)
   syn)


;------------------------------------------------------------------------------------------;
;------------------------------- Testing: -------------------------------;
;------------------------------------------------------------------------------------------;
(module+ test
  (require
   chk
   (only-in (submod "..")
            [turn-Type Type]
            [turn-define define]
            [turn-λ λ]
            [turn-Π Π]
            [turn-app #%app]
            [turn-axiom axiom]
            [turn-data data]
            [turn-new-elim new-elim]))


  ; -------------------- Top-level and Failure tests --------------------
  ; Test that top-level code, like define, data, and axiom expand successfully.
  ; Also test that failure tests, i.e. ill-typed code, produces the right error messages.
  ; These test must be run during the dynamic extent of the macro expansion in order to use
  ; local-expand.
  ; Using local-expand is necessary so that we can:
  ; 1. expand top-level code, like define, in an expression context, i.e. in a unit test
  ; 2. catch type errors produced by the macros during macro expansion, before a run-time unit test
  ;    can catch them.
  ; ---------------------------------------------------------------------
  (begin-for-syntax
    (require chk)
    (require (only-in rackunit require/expose))
    (require/expose turnstile/examples/dep-ind-fixed (assign-type))
    (define (expand/def syn)
      (local-expand syn 'top-level '()))
    (define (expand/term syn)
      (local-expand syn 'expression '()))

    (chk
     ;; --------------- Top-level should succeed ---------------
     ;;; Defines
     #:t (expand/def #'(define x (Type 1)))
     #:t (expand/def #'(define puppies (Type 2)))
     #:t (expand/def #'(define kittens (Type 3)))
     #:t (expand/def #'(define id (λ (x : (Type 2)) x)))
     #:t (expand/def #'(define id2 (λ (A : (Type 3)) (λ (a : A) a))))

     ;;; Axioms
     ;; TODO: Not sure why, but these have weird binding errors in them. Might be a Racket bug, have
     ;; to investigate furhter.
     ;; The same may apply to top-level data tests
     ;#:t (expand/def #'(axiom Nat : (Type 0)))
     ;#:t (expand/def #'(axiom z : Nat))
     ;#:t (expand/def #'(axiom s : (Π (y : Nat) Nat)))
     ;#:t (expand/def #'(axiom meow : (Π (x : (Type 1)) (Type 0))))


     ;#:t (expand/def #'(data Nat2 : 0  (Type 0)
     ;                        (z2 : Nat2)
     ;                        (s2 : (Π (x : Nat2) Nat2))))

       #|
fails:
dep-define-datatype: type mismatch: expected Type, given (Type 1)
  expression: (Type 0)
  at: (Type 0)
  in: (dep-define-datatype Nat2 : (Type 0) (z2 : Nat2) (s2 : (Π (x : Nat2) Nat2)))

|#




     ;#:t (expand/def #'(data Maybe : 1 (Π (A : (Type 0)) (Type 0))
     ;                        (none : (Π (A : (Type 0)) (Maybe A)))
     ;                        (just : (Π (A : (Type 0)) (Π (a : A) (Maybe A))))))
     #|
fails:
 dep-define-datatype: expected more terms
  at: ()
|#

     ;; --------------- Top-level should fail ------------------
     ;;; Defines
     #:x (expand/def #'(define y (define z (Type 1)) z))
     "define: unexpected term";\n  at: z"

     #:x (expand/def #'(define y (define z (Type 1) x) z))
     "define: unexpected term";\n  at: z"

     #:x (expand/def #'(define x Type))
     "Type: bad syntax";\n  in: Type"

     #:x (expand/def #'(define x (Type 1) (Type 1)))
     "define: unexpected term";\n  at: (Type 1)"

#|
     ;;; Axioms
     #:x (expand/def #'(axiom meow2 : ((Type 1) (Type 2))))
     "meow"

     #:x (expand/def #'(axiom meow3 : (λ (x : (Type 0)) x)))
     "meow"

     #:x (expand/def #'(define y (axiom Nat : (Type 0))))
     "meow"

|#
#|
     ;;; Inductives !!!

     #:x (expand/def #'(data Nat : 0 (Type 0)
                             (z : Nat)
                             (s : (Π (x : Nat) Nat))))
     "Nat already defined"

     #:x (expand/def #'(data Nat2 : 0 (Type 0)
                             (z : Nat2)
                             (s : (Π (x : Nat) Nat))))
     "z already defined"

     #:x (expand/def #'(data Nat2 : 0 (Type 0)
                             (z2 : Nat2)
                             (s2 : (Π (x : Nat) Nat))))
     "expected constructor for inductive definition Nat2 to return Nat2, but found Nat"

     #:x (expand/def #'(data Nat2 : 0 (id (Type 1))
                             (z2 : Nat2)
                             (s2 : (Π (x : Nat) Nat))))
     "expected telescope but found (id (Type 1))"

|#
     ;; --------------- Type should fail ------------------
     #:x (expand/term #'(Type z))
     "Type: expected exact-nonnegative-integer"

     #:x (expand/term #'(Type -1))
     "Type: expected exact-nonnegative-integer"



     ;; --------------- λ should fail --------------------
     ;; Consider this one failing as the error message produces is not good.
;     #:x (expand/term #'(λ (x : (λ (x : (Type 2)) x)) x)) ;fails: expected id
   ;  "λ: Expected term of type Type"
 ;    "Π: Expected Type type, got: (Π ((x : (Type 2))) (Type 2))" ;current error



     ;; --------------- app should fail ------------------
   ;  #:x (expand/term #'((λ (x : (Type 2)) x) (Type 3))) ;fails: expected id
    ; "app: type mismatch: expected (Type 2), given (Type 4)"

   ;  #:x (expand/term #'((λ (x : (Type 2)) x) (Type 2))) ;fails: expected id
    ; "app: type mismatch: expected (Type 2), given (Type 3)"

     ;; Bad error; bug in turnstile?
  ;   #:x (expand/term #'((Type 1) (Type 2)))
   ;  "app: expected term of function type" ;;current error: dep-#%app: expected the identifier `#%plain-app'

     ;; Bad error; bug in turnstile? Should probably instantiate A in error message
 ;    #:x (expand/term #'(((λ (A : (Type 3)) (λ (a : A) a)) (Type 2)) (Type 2)))
 ;    "app: type mismatch: expected (Type 2), given (Type 3)"

     ;; --------------- Π should fail ------------------
     #:x (expand/term #'(Π (x : (x (Type 1))) (Type 1)))
     "expected function but found x"

     #:x (expand/term #'(Π (x : (Type 1)) (x (Type 1))))
     "Expected ∀ type, got: (Type 1)"

;     #:x (expand/term #'(Π (y : (Type 1)) (y (Type 1))))
    ; "expected function but found y" ;currently
 ;    "unexpected term"

;     #:x (expand/term #'(Π (y : (λ (x : (Type 0)) x)) (Type 1))) ;fails: unexpected term
   ;  "expected a kind (a term whose type is a universe) but found a term of type (Π (x : (Type 0)) (Type 0))"
     ; "unexpected term"
     ))

  ;;;;;;;;;define should succeed;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; NB: These defines copy-pasted from above.
  (define x (Type 1))
  (define puppies (Type 2))
  (define kittens (Type 3))
  (define id (λ (x : (Type 2)) x)) ;^
  (define id2 (λ (A : (Type 3)) (λ (a : A) a))) ;^

  ;; -------------------- axioms should succeed --------------------
  (axiom Nat : (Type 0))
  (axiom z : Nat)
  (axiom s : (Π (y : Nat) Nat)) ;fails: unexpected term in: Nat (latter)
  (axiom meow : (Π (x : (Type 1)) (Type 0))) ;fails: unexpected term in (Type 0)
  (axiom Vec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0)))) ;fails: unexpected term in (Π (n : Nat) (Type 0))
  (axiom nil : (Π (A : (Type 0)) ((Vec A) z))) ;fails: unexpected term in ((Vec A) z)
  (axiom NotVec : (Π (A : (Type 0)) (Π (n : Nat) (Type 0)))) ;fails: unexpected term in  (Π (n : Nat) (Type 0))

 ; (define test1 (λ (a : (Π (x : Nat) Nat)) (a z))) ;dep-Π: unexected term in : Nat

  ;; -------------------- inductives should succeed ----------------
  (data Maybe : 1 (Π (A : (Type 0)) (Type 0))
        (none : (Π (A : (Type 0)) (Maybe A)))
        (just : (Π (A : (Type 0)) (Π (a : A) (Maybe A)))))

  (data Nat2 : 0 (Type 0)
        (z2 : Nat2)
        (s2 : (Π (x : Nat2) Nat2)))




  ; -------------------- Failing δ reduction and Γ tests --------------------
  ; These tests are specifically for δ reduction and typing that assume top-level definitions.
  ; They must remain after the phase 0 definitions and axioms that currently preceed them, but still
  ; must be run at phase 1.
  ; -----------------------------------------------------------------
  (begin-for-syntax
    (chk
     ;; --------------- Test definitions ---------------
     ;;; TODO: should add some that only give good errors when δ reduction occurs. Probably needs
     ;;; equality type for that
     #:x (expand/term #'(id id))
     "type mismatch: expected (Type 2), given (Π ((x : (Type 2))) (Type 2))"
     )
#|
    (chk
     ;; --------------- Test axioms -------------------
     #:x (expand/term #'(z (Type 0)))
     "expected function but found term of type Nat"

     #:x (expand/term #'(meow z))
     "expected term of type (Type 1) but found term of type Nat"

     ;; tests that inductives are generative, not structural.
     #:x (expand/term #'((λ (a : ((NotVec Nat) z)) z) (nil Nat)))
     "expected term of type NotVec but found term of type Vec"

     #:x (expand/term #'(test1 z))
     "expected term of type (Π (x : Nat) Nat) but found term of type Nat"
     )
|#
#|
    (chk

     ;; --------------- Test inductives ---------------
     #:x (expand/term #'(new-elim z (λ (x : Nat) Nat) (z (λ (n : Nat) n))))
     "expected target of inductive type, but found z of type Nat, which is not inductively defined"

     #:x (expand/term #'(new-elim z2 (λ (x : Nat2) Nat2)
                     (z2 (λ (n : Nat2) n))))
     "expected term of type (Π (x : Nat2) (Π (ih : Nat2) Nat)) when checking method"

     #:x (expand/term #'(new-elim (s2 z2) Nat2
                                  (z2 (λ (n : Nat2) n))))
     "expected function but found Nat2 when checking motive"

     #:x (expand/term #'(new-elim (s2 z2) (λ (x : Nat2) Nat2)
                                  (z2)))
     "expected 2 methods, one for each constructor, but found 1"

     #:x (expand/term #'(new-elim (s2 z2) (λ (x : Nat) Nat2)
                                  (z2)))
     "expected 2 methods, one for each constructor, but found 1"

     #:x (expand/term #'(new-elim (s2 z2) (λ (x : Nat) Nat2)
                                  (z2 (λ (n : Nat2) (λ (ih : Nat2)) n))))
     "expected type Nat2 but found type Nat when checking motive"

     #:x (expand/term #'(new-elim (s2 z2) (λ (x : Nat2) (λ (y : Nat) (Type 0)))
                                  (z2 (λ (x : Nat2) (λ (IH : Nat) IH)))))
     "expected kind but found (λ (y : Nat) (Type 0)) while checking motive"

     #:x (expand/term #'(new-elim (s2 z2) (λ (x : Nat2) Nat)
                                  (z2 (λ (x : Nat2) (λ (IH : Nat) IH)))))
     "expected type Nat2 but found type Nat when checking method"

     #:x (expand/term #'((λ (x : (new-elim z2 (λ (x : Nat2) (Type 1))
                                           ((Type 0) (λ (x : Nat2) (Type 0))))) x) Nat))
     "expected function but found (Type 0) when checking method"

)
|#
)


  (chk
   ;; ---------------  Test that definition evaluate ---------------
   ;;;;;;;;;;;;;; define should succeed and δ reduction ;;;;;
   #:= x (Type 1)
   #:= puppies (Type 2)
   #:= kittens (Type 3)
   ;; NB: Can't compare function values for equality; must test function equality indirectly.
;   #:= id (λ (x : (Type 2)) x)
   #:= (id (Type 1)) ((λ (x : (Type 2)) x) (Type 1))
;   #:= id2 (λ (A : (Type 3)) (λ (a : A) a))
   #:= ((id2 (Type 2)) (Type 1)) (((λ (A : (Type 3)) (λ (a : A) a)) (Type 2)) (Type 1))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Type should succeed;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   #:t (Type 0)

   #:t (Type 1)
   #:t (Type 3)

;;;;;;;;;;;;;;;;;;;; λ should succeed ;;;;;;;;;;;;;;;;;;;;

;;;gives "?: literal data is not allowed; no #%datum syntax transformer is bound in: #f"
;λs cannot return a type
;;;All these tests give that error (written in equivalent pairs to rule out previous defines):
;;;   #:t (λ (y : x) x) ;;this one was definitely supposed to succeed, the rest are mine
;;;   #:t (λ (y : (Type 1)) (Type 1))

;;;   #:t (λ (y : (Type 2)) kittens)
;;;   #:t (λ (y : (Type 2)) (Type 3))

;;;   #:t (λ (z : (Type 0)) x)
;;;   #:t (λ (z : (Type 0)) (Type 1))



;;but these do not:
 #:t (λ (z : x) z)
 #:t (λ (x : (Type 3)) x)
 #:t (λ (x : (Type 2)) (λ (y : (Type 0)) y))


;;;;;;;;;;;;;;;;;;;; app should succeed;;;;;;;;;;;;;;;
#:= ((λ (x : (Type 2)) x) (Type 1)) (Type 1) ;OK

;;;(note: puppes is (Type 2))
; NB: Can't test function equality directly
;#:= ((λ (A : (Type 3)) (λ (a : (Type 2)) a)) puppies) (λ (a : (Type 2)) a) ;???
#:= (((λ (A : (Type 3)) (λ (a : (Type 2)) a)) puppies) (Type 1)) ((λ (a : (Type 2)) a) (Type 1)) ;???

;;;(note: puppies is (Type 2), x is (Type 1))
#:= (((λ (A : (Type 3)) (λ (a : (Type 2)) a)) puppies) x) x ;???

#:= (id (Type 1)) (Type 1)
#:= ((id2 (Type 2)) (Type 1)) (Type 1)
#:= (id x) x


#:t (((λ (Nat : (Type 3))
        (λ (z : Nat)
          (λ (s : (Π (n : Nat) Nat))
            z)))
      (Type 2))
     (Type 1))


;;;;;;;;;;;;;;;;;;;; Π should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;
#:t (Π (x : (Type 1)) (Type 1)) ;OK
#:t (Π (x : (Type 1)) (Type 2)) ;OK
)
  (chk

;; -------------------- inductives should succeed --------------------
;#:t z2
#:t ((just Nat) z)
;#:t ((λ (f : (Π (A : (Type 0)) (Type 0))) z) Maybe)
)
#; (chk
;;;;;;;;;;;;;;;;;;;; axiom should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;

#:t z
#:t meow
#:t (nil Nat)
#:t ((λ (a : ((Vec Nat) z)) z) (nil Nat))
#:t s
#:t (test1 s)

)
 #; (chk

;;;;;;;;;;;;;;;;;;;; elim should succeed ;;;;;;;;;;;;;;;;;;;;;;;;;
;#:= (new-elim (s2 z2) (λ (x : Nat2) Nat2)
;              ((s2 z2) (λ (n : Nat2) (λ (IH : Nat2) (s2 IH)))))
;(s2 z2)

#:= (new-elim ((none Nat))
              (λ (λ (x : (Maybe Nat)) Nat))
              ((λ (λ (λ z)))
               (λ (λ (a : Nat) (λ a)))))
z

#:= (new-elim ((just Nat) (s z)) (λ (λ (x : (Maybe Nat)) Nat))
              ((λ (λ (λ z)))
               (λ (λ (a : Nat) (λ a)))))
(s z)

;#:= ((λ (x : (new-elim (s2 z2) (λ (x : Nat2) (Type 1))
;                       ((Type 0) (λ (x : Nat2) (λ (IH : (Type 1)) IH))))) x) Nat)
;Nat

))
