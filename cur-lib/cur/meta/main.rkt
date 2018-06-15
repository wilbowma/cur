#lang s-exp "../main.rkt"

(require
 (only-in
  "../main.rkt"
  [begin core-begin]
  [define core-define]
  [data core-data]
  [Type core-Type]
  [Π core-Π]
  [λ core-λ]
  [#%app core-app]
  [new-elim core-elim])
 "../stdlib/sugar.rkt"
 "../stdlib/nat.rkt"
 "../stdlib/list.rkt")

;; Staged meta-programming for Cur
;; Largely based on
;; anand2018 - Towards Certified Meta-Programming
;; with Typed Template-Coq

(data Cur-Level : 0 (Type 0)
      (level-z : Cur-Level)
      (level-s : (-> Cur-Level Cur-Level)))

;; Hm, need strings to do this right
;; Trying De bruijn for now
(data Cur-Name : 0 (Type 0)
      (cur-id : (-> Nat Cur-Name))) 

(data Cur-Term : 0 (Type 0)
      (cur-type : (-> Cur-Level Cur-Term))
      (cur-var : (-> Cur-Name Cur-Term))
      (cur-const : (-> Cur-Name Cur-Term))
      (cur-lam : (-> Cur-Name Cur-Term Cur-Term))
      (cur-app : (-> Cur-Term Cur-Term Cur-Term))
      (cur-Pi : (->  Cur-Name Cur-Term Cur-Term))
      (cur-elim : (-> Cur-Term Cur-Term (List Cur-Term) Cur-Term)))

(data Cur-Program : 0 (Type 0)
      (cur-data : (-> Nat Cur-Term (List (Pair Cur-Name Cur-Term)) Cur-Program))
      (cur-def : (-> Cur-Name Cur-Term Cur-Program))
      (cur-expr : (-> Cur-Term Cur-Program))
      (cur-eof : Cur-Program))

;; Really ought to provide some pattern expanders
;; quasiquote expects either a Cur Program or a Cur term, and an optional a map from free vars to Cur-Names
(begin-for-syntax
  (define (quasiquote/program syn free-var-map)
    (let quasiquote/program ([syn syn])
      (syntax-parse (cur-expand syn)
        #:literals (core-Type core-Π core-λ core-app core-elim core-begin core-data core-define)
        #:datum-literals (:)
        [(core-data x:id : p:nat D (cs:id : e) ...)
         #`(cur-data p #,(quasisquote/term #'D)
                     (make-list
                      (make-pair cs (quasiquote e)) ...))]
        [(core-define x:id e)
         ]
        [_ (quasiquote/term this-syntax free-var-map)])))

  (define (quasiquote/term syn free-var-map)
    (let quasiquote/term ([syn syn])
      (syntax-parse (cur-expand syn)
        #:literals (core-Type core-Π core-λ core-app core-elim core-begin core-data core-define)
        #:datum-literals (:)
        [(core-Type i:nat)
         #`(cur-type #,(nat->level #'i))]
        [x:id
         #:when (member #'x free-var-map)
         (ref #'x free-var-map)]
        [(core-λ )]
        [(core-app )]
        [(core-Π (x:id : A) B)
         #`(cur-Pi (cur-id z)
                   #,(quasiquote/term #'A)
                   #,(shift (quasiquote/term (subst #'(cur-var (cur-id z)) #'x #'B))))]
        [(core-elim )]))))

(define-syntax (quasiquote syn)
  (syntax-parse syn
    #:literals (core-Type core-Π core-λ core-app core-elim core-begin core-data core-define)
    #:datum-literals (:)
    [(_ p:cur-program (~optional fv-map))
     (quasiquote/program #'p (or (attribute fv-map) empty-map))]
    [(_ t:cur-term (~optional fv-map))
     (quasiquote/term #'t (or (attribute fv-map) empty-map))]))
