#lang s-exp "cur-redex.rkt"

;; Use racket libraries over your dependently typed code!?!?
;; TODO: actually, I'm not sure this should work quite as well as it
;; seems to with check-equal?
(require rackunit)
(require (only-in "cur-redex.rkt" [#%app real-app]
                  [define real-define]))

(define-syntax (#%app syn)
  (syntax-case syn ()
    [(_ e1 e2)
     #'(real-app e1 e2)]
    [(_ e1 e2 e3 ...)
     #'(#%app (#%app e1 e2) e3 ...)]))

;; -------------------
;; Define inductive data

(data true : Type (T : true))

(data false : Type)

;; -------------------
;; Look, syntax extension!
(define-syntax (-> syn)
  (syntax-case syn ()
    [(_ t1 t2)
     (with-syntax ([(x) (generate-temporaries '(1))])
       #`(forall (x : t1) t2))]))

(data nat : Type
  (z : nat)
  (s : (-> nat nat)))

(define nat-is-now-a-type
  (lambda (y : (-> nat nat))
    (lambda (x : nat) (y x))))

;; -------------------
;; Lexical scoping! I can reuse the name nat!

(define nat-is-just-a-name (lambda (nat : Type) nat))

;; -------------------
;; Reuse some familiar syntax

(define y (lambda (x : true) x))
;(define (y1 (x : true)) x)
;(define (y2 (x1 : true) (x2 : true)) x1)

;; -------------------
;; Unit test dependently typed code!

(check-equal? (y2 T T) T)

;; -------------------
;; Write functions on inductive data
(define (add1 (n : nat)) (s n))

(check-equal? (add1 (s z)) (s (s z)))

(define (sub1 (n : nat))
  (case n
    [z z]
    [s (lambda (x : nat) x)]))
(check-equal? (sub1 (s z)) z)

(define plus
  (fix (plus : (forall (n1 : nat) (forall (n2 : nat) nat)))
    (lambda (n1 : nat)
      (lambda (n2 : nat)
        (case n1
          [z n2]
          [s (λ (x : nat) (plus x (s n2)))])))))

(check-equal? (plus (s (s z)) (s (s z))) (s (s (s (s z)))))

;; -------------------
;; It's annoying to have to write things explicitly curried
;; Macros to the rescue!

(define-syntax forall*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (forall (a : t)
        (forall* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax lambda*
  (syntax-rules (:)
    [(_ (a : t) (ar : tr) ... b)
     (lambda (a : t)
       (lambda* (ar : tr) ... b))]
    [(_ b) b]))

(define-syntax (define syn)
  (syntax-case syn ()
    [(define (name (x : t) ...) body)
     #'(real-define name (lambda* (x : t) ... body))]
    [(define id body)
     #'(real-define id body)]))

(data and : (forall* (A : Type) (B : Type) Type)
  (conj : (forall* (A : Type) (B : Type)
            (x : A) (y : B) (and A B))))

;; -------------------
;; Prove interesting theorems!

(define (thm:and-is-symmetric
          (x : (forall* (P : Type) (Q : Type)
                 ;; TODO: Can't use -> for the final clause because generated
                 ;; name has to match name in proof.
                 (ab : (and P Q))
                 (and P Q))))
  T)

(define proof:and-is-symmetric
  (lambda* (P : Type) (Q : Type) (ab : (and P Q))
    (case ab
      (conj (lambda* (P : Type) (Q : Type) (x : P) (y : Q) (conj Q P y x))))))

(check-equal? (thm:and-is-symmetric proof:and-is-symmetric) T)


;; -------------------
;; Ugh, why did the language implementer make the syntax for case so stupid?
;; I wish I could fix that ... Oh I can.
(begin-for-syntax
  (define (rewrite-clause clause)
    (syntax-case clause (:)
      [((con (a : A) ...) body) #'(con (lambda* (a : A) ... body))]
      [(e body) #'(e body)])))
(define-syntax (case* syn)
  (syntax-case syn ()
    [(_ e clause* ...)
     #`(case e #,@(map rewrite-clause (syntax->list #'(clause* ...))))]))

(define proof:and-is-symmetric^
  (lambda* (S : Type) (R : Type) (ab : (and S R))
    (case* ab
      [(conj (S : Type) (R : Type) (s : S) (r : R))
       (conj R S r s)])))

(check-equal? (thm:and-is-symmetric proof:and-is-symmetric^) T)

;; -------------------
;; Gee, I wish there was a special syntax for theorems and proofs so I could think of
;; them as seperate from types and programs.

(define-syntax-rule (define-theorem name prop)
  (define name prop))

(define-syntax-rule (qed thm pf)
  (check-equal? T ((lambda (x : thm) T) pf)))

(define-theorem thm:and-is-symmetric^^
  (forall* (P : Type) (Q : Type) (ab : (and P Q)) (and Q P)))

(qed thm:and-is-symmetric^^ proof:and-is-symmetric)

(define-theorem thm:proj1
  (forall* (A : Type) (B : Type) (c : (and A B)) A))
(define proof:proj1
  (lambda* (A : Type) (B : Type) (c : (and A B))
    (case c (conj (lambda* (A : Type) (B : Type) (a : A) (b : B) a)))))
(qed thm:proj1 proof:proj1)

(define-theorem thm:proj2
  (forall* (A : Type) (B : Type) (c : (and A B)) B))
(define proof:proj2
  (lambda* (A : Type) (B : Type) (c : (and A B))
    (case c (conj (lambda* (A : Type) (B : Type) (a : A) (b : B) b)))))
(qed thm:proj2 proof:proj2)

;; -------------------
;; Gee, I wish I had special syntax for defining types like I do for
;; defining functions.

(define-syntax-rule (define-type (name (a : t) ...) body)
  (define name (forall* (a : t) ... body)))

(define-type (not (A : Type)) (-> A false))

#|
;;TODO: Can't pattern match on a inductive with 0 constructors yet.
(define-theorem thm:absurd
  (forall* (P : Type) (A : Type) (a : A) (~a : (not A)) P))
(qed thm:absurd (lambda* (P : Type) (A : Type) (a : A) (~a : (not A))
       (case (~a a))))

(define-theorem thm:absurdidty
  (forall* (P : Type) (A : Type) (a*nota : (and A (not A))) P))

;; TODO: Not sure why this doesn't type-check.. probably not handling
;; inductive families correctly in (case ...)
(define (proof:absurdidty (P : Type) (A : Type) (a*nota : (and A (not A))))
  ((proof:proj2 A (not A) a*nota) (proof:proj1 A (not A) a*nota)))
|#

;; -------------------
;; Automate theorem proving! With real meta-programming, syntax is just data.

(define-syntax (inhabit-type syn)
  (syntax-case syn (true false nat forall :)
    [(_ true) #'T]
    [(_ nat) #'z]
    [(_ false)
     (raise-syntax-error 'inhabit
       "Actually, this type is unhabited" syn)]
    ;; TODO: We want all forall*s to be expanded by this point. Should
    ;; look into Racket macro magic to expand syn before matching on it.
    [(_ (forall (x : t0) t1))
     ;; TODO: Should carry around assumptions to enable inhabit-type to use
     ;; them
     #'(lambda (x : t0) (inhabit-type t1))]
    [(_ t)
     (raise-syntax-error 'inhabit
       "Sorry, this type is too much for me" syn)]))

;; TODO: Would be great if meta-programs could reference things by name.
;; e.g. if I run (inhabit-type thm:true-is-proveable), it would first
;; lookup the syntax of the definition thm:true-is-proveable, then
;; run ... this would require some extra work in define, and a macro for
;; defining macros this way.
(define-theorem thm:true-is-proveable true)
(qed thm:true-is-proveable (inhabit-type true))

(define-theorem thm:anything-implies-true (forall (P : Type) true))
(qed thm:true-is-proveable (inhabit-type (forall (P : Type) true)))

#;(define is-this-inhabited? (inhabit-type false))

;; -------------------
;; Unit test your theorems before proving them!

(define-syntax ->*
  (syntax-rules ()
    [(->* a) a]
    [(->* a a* ...)
     (-> a (->* a* ...))]))

(define-theorem thm:true?
  (forall* (A : Type) (B : Type) (P : Type)
    ;; If A implies P and (and A B) then P
    (->* (-> A P) (and A B) P)))

(qed (thm:true? true true true)
     ;; TODO: inhabit-type ought to be able to reduce (type-thm:true? true true true)
     ;; but can't. Maybe instead there should be a reduce tactic/macro.
     (inhabit-type (forall (a : (-> true true))
                   (forall (f : (and true true))
                   true))))

;; -------------------
;; Okay but what about *real* proofs, like formalizing STLC, complete
;; with fancy syntax?

(data type : Type
  (Unit : type)
  (Pair : (->* type type type))
  (Fun  : (->* type type type)))

(data var : Type
  (v : (-> nat var)))

(data term : Type
  (tvar : (-> var term))
  (unitv : term)
  (pair  : (->* term term term))
  (lam   : (->* var type term term))
  (prj   : (->* nat term term))
  (app   : (->* term term term)))

;; Now, fancy syntax to write these terms in a more natural syntax,
;; instead of via applications of inductives. Also, use variables names
;; and automatically get de Bruijn indecies.
(begin-for-syntax
  (define index #'z))
(define-syntax (begin-stlc syn)
  (set! index #'z)
  (let stlc ([syn (syntax-case syn () [(_ e) #'e])])
    (syntax-case syn (lambda : prj * -> quote)
      [(lambda (x : t) e)
       (let ([oldindex index])
         (set! index #`(s #,index))
         #`((lambda (x : term)
              (lam (v #,oldindex) #,(stlc #'t) #,(stlc #'e)))
            (tvar (v #,oldindex))))]
      [(quote (e1 e2))
       #`(pair #,(stlc #'e1) #,(stlc #'e2))]
      [(prj i e1)
       #`(prj i #,(stlc #'e1))]
      [() #'unitv]
      [(t1 * t2)
       #`(Pair #,(stlc #'t1) #,(stlc #'t2))]
      [(t1 -> t2)
       #`(Fun #,(stlc #'t1) #,(stlc #'t2))]
      [(e1 e2)
       #`(app #,(stlc #'e1) #,(stlc #'e2))]
      [e
       (if (eq? 1 (syntax->datum #'e))
           #'Unit
           #'e)])))

(check-equal?
  (begin-stlc (lambda (x : 1) x))
  (lam (v z) Unit (tvar (v z))))
(check-equal?
  (begin-stlc ((lambda (x : 1) x) ()))
  (app (lam (v z) Unit (tvar (v z))) unitv))
(check-equal?
  (begin-stlc '(() ()))
  (pair unitv unitv))

;; ---------------

(data gamma : Type
  (emp-gamma : gamma)
  (ext-gamma : (->* gamma var type gamma)))

(data maybe : (forall (A : Type) Type)
  (none : (forall (A : Type) (maybe A)))
  (some : (forall* (A : Type) (a : A) (maybe A))))

(data bool : Type
  (btrue : bool)
  (bfalse : bool))

(define-syntax (if syn)
  (syntax-case syn ()
    [(_ t s f)
     #'(case t
         [btrue s]
         [bfalse f])]))

(define-syntax (define-rec syn)
  (syntax-case syn (:)
    [(_ (name (a : t) ... : t_res) body)
     #'(define name (fix (name : (forall* (a : t) ... t_res))
                      (lambda* (a : t) ... body)))]))

(define-rec (nat-equal? (n1 : nat) (n2 : nat) : bool)
  (case* n1
    [z (case* n2
         [z btrue]
         [(s (n3 : nat)) bfalse])]
    [(s (n3 : nat))
       (case* n2
         [z btrue]
         [(s (n4 : nat)) (nat-equal? n3 n4)])]))

(define (var-equal? (v1 : var) (v2 : var))
  (case* v1
    [(v (n1 : nat))
     (case* v2
       [(v (n2 : nat))
        (nat-equal? n1 n2)])]))

(define-rec (lookup-gamma (g : gamma) (x : var) : (maybe type))
  (case* g
    [emp-gamma (none type)]
    [(ext-gamma (g1 : gamma) (v1 : var) (t1 : type))
     (if (var-equal? v1 x)
         (some type t1)
         (lookup-gamma g1 x))]))

(define extend-gamma ext-gamma)

(data == : (forall* (A : Type) (x : A) (-> A Type))
  (refl : (forall* (A : Type) (x : A) (== A x x))))

#|
(data has-type : (->* gamma term type Type)
  (T-Unit : (forall* (g : gamma) (has-type g unitv Unit)))
  ....)
|#

;; Those inferrence rules look terrible. Gee, it would be great if I
;; could write them in a more natural, math notation....

(begin-for-syntax
  (define-syntax-class dash
    (pattern x:id
           #:fail-unless (regexp-match #rx"-+" (symbol->string (syntax-e #'x)))
           "Invalid dash"))

  (define-syntax-class decl (pattern (x:id (~datum :) t:id)))

  ;; TODO: Automatically infer decl ... by binding all free identifiers?
  (define-syntax-class inferrence-rule
    (pattern (d:decl ...
              x*:expr ...
              line:dash lab:id
              (name:id y* ...))
              #:with rule #'(lab : (forall* d ...
                                     (->* x* ... (name y* ...)))))))

(define-syntax (define-relation syn)
  (syntax-parse syn
    [(_ (n:id types* ...) rules:inferrence-rule ...)
     #:fail-unless (andmap (curry equal? (length (syntax->datum #'(types* ...))))
                           (map length (syntax->datum #'((rules.y* ...)
                                                          ...))))
     "Mismatch between relation declared and relation definition"
     #:fail-unless (andmap (curry equal? (syntax->datum #'n))
                           (syntax->datum #'(rules.name ...)))
     "Mismatch between relation declared name and result of inference rule"
      #`(data n : (->* types* ... Type)
          rules.rule ...)]))

(define-relation (has-type gamma term type)
  [(g : gamma)
   ------------------------ T-Unit
   (has-type g unitv Unit)]

  [(g : gamma) (x : var) (t : type)
   (== (maybe type) (lookup-gamma g x) (some type t))
   ------------------------ T-Var
   (has-type g (tvar x) t)]

  [(g : gamma) (e1 : term) (e2 : term) (t1 : type) (t2 : type)
   (has-type g e1 t1)
   (has-type g e2 t2)
   ---------------------- T-Pair
   (has-type g (pair e1 e2) (Pair t1 t2))]

  [(g : gamma) (e : term) (t1 : type) (t2 : type)
   (has-type g e (Pair t1 t2))
   ----------------------- T-Prj1
   (has-type g (prj z e) t1)]

  [(g : gamma) (e : term) (t1 : type) (t2 : type)
   (has-type g e (Pair t1 t2))
   ----------------------- T-Prj2
   (has-type g (prj (s z) e) t1)]

  [(g : gamma) (e1 : term) (t1 : type) (t2 : type) (x : var)
   (has-type (extend-gamma g x t1) e1 t2)
   ---------------------- T-Fun
   (has-type g (lam x t1 e1) (Fun t1 t2))]

  [(g : gamma) (e1 : term) (e2 : term) (t1 : type) (t2 : type)
   (has-type g e1 (Fun t1 t2))
   (has-type g e2 t1)
   ---------------------- T-App
   (has-type g (app e1 e2) t2)])
