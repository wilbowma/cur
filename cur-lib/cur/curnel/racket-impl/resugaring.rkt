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
     (displayln e)
     (displayln x)
       (if (pair? x)
           (last x)
           x))]
    [else e]))

(define-for-syntax (resugar syn)
  (syntax-parse syn
    #:datum-literals (#%app lambda quote #%expression)
    [x:id (origin-or syn)]
    [(#%expression e)
     (resugar #'e)]
    [(quote e)
     (origin-or #'e)]
    [(#%app f a)
     #:when (not (syntax-property syn 'origin))
     #`(#,(resugar #'f) #,(resugar #'a))]
    [(#%app f a)
;     #:when (syntax-property #'f 'constructor-for)
     #`(#,(origin-or syn) #,(resugar #'a))]
    [(lambda (x) body)
     #`(#,(origin-or syn) (#,(resugar #'x))
        #,(resugar #'body))]
    [_ syn]))

(define-syntax (origin syn)
  (syntax-case syn ()
    [(_ e)
     (begin 
       (printf "Expanded ~a~n" (syntax->datum (local-expand #'e 'expression null)))
       (printf "Resugared ~a~n" (syntax->datum (resugar (local-expand #'e 'expression null))))
       #'(void))]))

(struct meow (e))

(origin (list 1))

(origin (meow 1))

(origin (λ (x) x))

(define-syntax (λ* syn)
  (syntax-case syn ()
    [(_ () body)
     #`body]
    [(_ (x xs ...) body)
     #`(lambda (x) (λ* (xs ...) body))]))

(define-syntax (app* syn)
  (syntax-case syn ()
    [(_ e)
     #`e]
    [(_ e1 e2 es ...)
     #`(app* (e1 e2) es ...)]))

(define-syntax (my-let syn)
  (syntax-case syn ()
    [(_ ([x e] ...) body)
     #`(app* (λ* (x ...) body) e ...)]))

;; Okay so, resugaring could work over the curnel, but not for arbitrary macros... but even then, I'm
;; skeptical. Might end up with very bad error messages, but at the very least could use to blame the
;; right macro.
(origin (my-let ([x 5] [y 6]) y))
