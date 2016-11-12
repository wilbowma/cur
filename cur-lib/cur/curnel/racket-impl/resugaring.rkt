#lang racket
(require
 (for-syntax
  racket/list
  syntax/parse))

;; On the Origin of Syntax
(define-for-syntax (origin-or e)
  (cond
    [(syntax-property e 'origin)
     =>
     (lambda (x)
       (if (pair? x)
           (last x)
           x))]
    [else e]))

(define-for-syntax (resugar syn)
  (syntax-parse syn
    #:datum-literals (#%app lambda quote)
    [x:id (origin-or syn)]
    [(quote e)
     (origin-or #'e)]
    [(#%app f a)
     #:when (not (syntax-property #'f 'constructor-for))
     #`(#,(resugar #'f) #,(resugar #'a))]
    [(#%app f a)
     #:when (syntax-property #'f 'constructor-for)
     #`(#,(origin-or syn) #,(resugar #'a))]
    [(lambda (x) body)
     #`(#,(origin-or syn) (#,(resugar #'x))
        #,(resugar #'body))]
    [_ syn]))

(define-syntax (origin syn)
  (syntax-case syn ()
    [(_ e)
     (begin 
       (printf "Expanded ~a~n" (local-expand #'e 'expression null))
       (printf "Resugared ~a~n" (resugar (local-expand #'e 'expression null)))
       #'(void))]))

(struct meow (e))

(origin (list 1))

(origin (meow 1))

(origin (λ (x) x))
