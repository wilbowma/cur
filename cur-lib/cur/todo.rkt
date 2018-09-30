#lang s-exp "main.rkt"

(require
 "curnel/racket-impl/runtime.rkt"
 (for-syntax todo-list "curnel/racket-impl/runtime-utils.rkt"))

(provide TODO)

(data False : 0 (Type 0))
(axiom BADNESS10000 : False)

(define-for-syntax (pretty-print-env g)
  (for/fold
      ([str ""])
      ([(k v) (in-dict g)])
    (format "~a~a : ~a~n" str (syntax-e k) (syntax-e (identifier-info-type v)))))

(define-for-syntax (hline str)
  (build-string (max (sub1 (string-length str)) 0) (lambda _ #\-)))

(define-syntax (TODO stx)
  (syntax-parse stx
    [(_ type) #`(TODO type "TODO: Something of type ~a.")]
    [(_ type msg)
     (let* ([env (pretty-print-env (gamma))]
            [item (todo-item (format "~a~a~n~a"
                                     env
                                     (hline env)
                                     (syntax-e #'type))
                             (format (syntax-e #'msg)
                                     (syntax-e #'type)))])
       (syntax-property
        #`(new-elim BADNESS10000 (λ (x : False) type))
        'todo
        item
        #t))]))

(require "stdlib/nat.rkt")
(TODO Nat)
