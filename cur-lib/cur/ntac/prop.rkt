#lang s-exp "../main.rkt"
(require
 "../stdlib/sugar.rkt"
 "../stdlib/prop.rkt"
 "base.rkt"
 "standard.rkt"
  (for-syntax "../curnel/racket-impl/stxutils.rkt"
              (for-syntax syntax/parse)))

(provide (for-syntax reflexivity by-rewrite rewrite))

;; require equality (==) from cur/stdlib/prop
(begin-for-syntax

  (define-syntax ~==
    (pattern-expander
     (syntax-parser
       [(_ ty a b)
        #'(_ (_ (_ (~literal ==) ty) a) b)])))
  
  ;; `reflexivity` is defined here instead of standard.rkt
  ;; because it requires cur/stdlib/prop
  (define (reflexivity ptz)
    (match-define (ntt-hole _ goal) (nttz-focus ptz))
    (ntac-match goal
     ;; TODO: use pattern expanders to abstract away these #%app's?
     [(_ (_ (_ (~literal ==) ty) a) b)
      ((fill (exact #'(refl ty a))) ptz)]))

  ;; TODO: currently can only do ids, and only left to right
  (define-syntax (by-rewrite syn)
    (syntax-case syn ()
      [(_ x)
       #`(fill (rewrite #'x))]))

  (define ((rewrite name) ctxt pt)
    (match-define (ntt-hole _ goal) pt)
;    (printf "goal = ~a\n" (syntax->datum goal))
;    (displayln (syntax->datum (dict-ref ctxt name)))
    (ntac-match (dict-ref ctxt name)
     [(_ (_ (_ (~literal ==) ty) a:id) b)#;((~literal ==) ty a:id b)
      (with-syntax ([a* (generate-temporary #'a)])
        (make-ntt-apply
         goal
         (list (make-ntt-hole (cur-rename #'b #'a goal)))
         (λ (body-pf)
;          (printf "body pf = ~a\n" (syntax->datum body-pf))
           (quasisyntax/loc goal 
             (new-elim #,name
                       (λ [a : ty]
                         (λ [b : ty]
                           (λ [p : (== ty a b)]
                             #,goal)))
                       (λ [b : ty] #,body-pf))))))])))
