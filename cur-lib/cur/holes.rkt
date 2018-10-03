#lang s-exp "main.rkt"

(require
 "curnel/racket-impl/runtime.rkt"
 "curnel/racket-impl/reflection.rkt"
 (for-syntax todo-list "curnel/racket-impl/runtime-utils.rkt"))

(provide
 TODO
 (rename-out (TODO ?)))

(define-for-syntax (pretty-print-env g)
  (for/fold
      ([str ""])
      ([(k v) (in-dict g)])
    (format "~a~a : ~a~n" str (syntax-e k) (cur->datum (identifier-info-type v)))))

(define-for-syntax current-min-hrule-length (make-parameter 5))
(define-for-syntax (hrule str)
  (let ([m (for/fold
               ([n (current-min-hrule-length)])
               ([s (string-split str "\n")])
             (max n (string-length s)))])
    (build-string m (lambda _ #\-))))

(define-for-syntax current-hole-counter (make-parameter 0))
(define-for-syntax (inc-hole-counter!) (current-hole-counter (+ 1 (current-hole-counter))))
(define-for-syntax (reset-hole-counter!) (current-hole-counter 0))
(define-for-syntax (new-hole-id! ctx)
  (inc-hole-counter!)
  (format-id ctx "HOLE~a" (current-hole-counter) #:source ctx))

(define-for-syntax (splice-new-type src f)
  (with-syntax ([HOLE (new-hole-id! src)])
    (quasisyntax
      (begin
        (axiom HOLE : (Type 0))
        #,(f #'HOLE)))))

(define-for-syntax current-default-hole-fmsg (make-parameter "TODO: Something of type ~a."))

(define-for-syntax (make-hole src [type #f] [fmsg #f])
  (define (make-hole-of-type type)
    (let* ([t (syntax-e type)]
           [fmsg (if fmsg (syntax-e fmsg) (current-default-hole-fmsg))]
           [env (pretty-print-env (gamma))]
           [item (todo-item (format "~a~a~n~a" env (hrule env) t)
                            (format fmsg t))])
      (with-syntax ([HOLE (new-hole-id! src)])
        (quasisyntax
         (begin
           (axiom HOLE : #,type)
           #,(syntax-property (syntax/loc src HOLE) 'todo item #t))))))

  (if type
      (make-hole-of-type type)
      (splice-new-type src make-hole-of-type)))

(define-syntax (TODO stx)
  (syntax-parse stx
    [(_ . ((~alt
            (~optional (~seq #:type type))
            (~optional (~seq #:fmsg fmsg))) ...))
     (make-hole stx (attribute type) (attribute fmsg))]
    [_ (make-hole stx)]))
