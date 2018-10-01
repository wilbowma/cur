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
  (let ([m (for/fold
               ([n 0])
               ([s (string-split str "\n")])
             (max n (string-length s)))])
    (build-string m (lambda _ #\-))))
(begin-for-syntax
  (module+ test
    (require chk)
    (chk
     #:= "-----" (hline (format "12345~n1234"))
     #:= "-----" (hline "12345\n1234")
     #:= "----" (hline "1234\n1234")
     #:= "----" (hline "123\n1234")
     #:= "-----" (hline "123\n1234\n12345")
     #:= "" (hline ""))))

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
