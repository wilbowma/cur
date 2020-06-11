#lang racket

(provide print-sz check-noninf-sz)

(require (for-syntax syntax/parse))

(define-syntax print-sz
  (syntax-parser
    [(_ e)
     #:with e+ (local-expand #'e 'expression null)
     #:with ty (let L ([tys (syntax-property #'e+ ':)])
                 (if (pair? tys)
                     (L (car tys))
                     tys))
     #:with sz (syntax-property #'ty '$)
     #:do[;(printf "term: ~a\n" (syntax->datum #'e))
          ;(printf "type: ~a\n" (syntax->datum #'ty))
          ;(printf "keys: ~a\n" (syntax-property-symbol-keys #'e+))
          ;(printf "keys2: ~a\n" (syntax-property-symbol-keys #'ty))
          (printf "size: ~a\n" (syntax->datum #'sz))]
     #'(void)]))

(define-syntax check-noninf-sz
  (syntax-parser
    [(_ e)
     #:with e+ (local-expand #'e 'expression null)
     #:with ty (let L ([tys (syntax-property #'e+ ':)])
                 (if (pair? tys)
                     (L (car tys))
                     tys))
     #:fail-unless (syntax-property #'ty '$)
                   (format "~a's type ~a has no size"
                           (syntax->datum #'e)
                           (syntax->datum (syntax-property #'ty 'orig)))
     #'(void)]))
