#lang cur
(require (for-syntax syntax/parse)
         cur/stdlib/sugar
         rackunit)
(provide check-type (all-from-out rackunit))

(define-syntax (check-type stx)
  (syntax-parse stx
    [(_ e (~datum :) ty)
     (syntax/loc stx (check-equal? (void) (:: e ty)))]))
  
