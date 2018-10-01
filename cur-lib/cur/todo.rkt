#lang s-exp "main.rkt"

(require
 "curnel/racket-impl/runtime.rkt"
 "curnel/racket-impl/reflection.rkt"
 (for-syntax todo-list "curnel/racket-impl/runtime-utils.rkt"))

(provide TODO)

(data False : 0 (Type 0))
(axiom HOLE : False)

(define-for-syntax (pretty-print-env g)
  (for/fold
      ([str ""])
      ([(k v) (in-dict g)])
    (format "~a~a : ~a~n" str (syntax-e k) (cur->datum (identifier-info-type v)))))

(define-for-syntax (hline str)
  (build-string (max (sub1 (string-length str)) 0) (lambda _ #\-)))

(define-syntax (TODO stx)
  (syntax-parse stx
    [(_ type)
     (syntax/loc stx
       (TODO type "TODO: Something of type ~a."))]
    [(_ type msg)
     (let* ([t (syntax-e #'type)]
            [env (pretty-print-env (gamma))]
            [item (todo-item (format "~a~a~n~a" env (hline env) t)
                             (format (syntax-e #'msg) t))])
       (syntax-property
        (syntax/loc stx (new-elim HOLE (λ (x : False) type)))
        'todo
        item
        #t))]))
