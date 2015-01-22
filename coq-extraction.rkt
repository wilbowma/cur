#lang s-exp "redex-core.rkt"

(begin-for-syntax
  (define orig-insp (variable-reference->module-declaration-inspector
    (#%variable-reference)))

  (define (disarm syn) (syntax-disarm syn orig-insp))

  ;; TODO: Pull expand, perhaps list of literals, into a library.
  (define (expand syn)
    (disarm (local-expand syn 'expression (syntax-e #'(lambda forall data case fix Type #%app #%top)))))

  (define (output-coq syn)
    (syntax-parse (expand syn)
       [((~literal lambda) ~! (x:id (~datum :) t) body:expr)
        (format "(fun ~a : ~a => ~a)" (syntax-e #'x) (output-coq #'t)
                (output-coq #'body))]
       [((~literal forall) ~! (x:id (~datum :) t) body:expr)
        (format "(forall ~a : ~a, ~a)" (syntax-e #'x) (output-coq #'t)
                (output-coq #'body))]
       [((~literal data) ~! n:id (~datum :) t (x*:id (~datum :) t*) ...)
        (format "Inductive ~a : ~a :=~n~a."
                (syntax-e #'n)
                (output-coq #'t)
                (string-trim
                  (for/fold ([strs ""])
                            ([clause (syntax->list #'((x* : t*) ...))])
                    (syntax-parse clause
                      [(x (~datum :) t)
                       (format "~a~a : ~a~n| " strs (syntax-e #'x)
                               (output-coq #'t))]))
                  #px"\\s\\| $"
                  #:left? #f))]
       ;; TODO: Add "case". Will be slightly tricky since the syntax is
       ;; quite different from Coq.
       [(e1 e* ...)
        (format "(~a~a)" (output-coq #'e1)
          (for/fold ([strs ""])
                    ([arg (syntax->list #'(e* ...))])
            (format "~a ~a" strs (output-coq arg))))]
       [e:id (format "~a" (syntax->datum #'e))])))

(define-syntax (generate-coq syn)
  (syntax-parse syn
    [(_ (~optional (~seq #:file file)) body:expr)
     (parameterize ([current-output-port (if (attribute file)
                                             (syntax->datum #'file)
                                             (current-output-port))])
       (displayln (output-coq #'body))
       #'Type)]))

(module+ test
  (require "sugar.rkt" "pltools.rkt")
  (begin-for-syntax
    (require rackunit)
    (check-equal?
      (format "Inductive nat : Type :=~nz : nat.")
      (output-coq #'(data nat : Type (z : nat))))
    (check-regexp-match
      "(forall .+ : Type, Type)"
      (output-coq #'(-> Type Type)))
    ;; TODO: Not sure why these tests are failing.
    (let ([t (output-coq #'(define-relation (meow gamma term type)
                             [(g : gamma) (e : term) (t : type)
                              --------------- T-Bla
                              (meow g e t)]))])
      (check-regexp-match
        "Inductive meow : (forall temp. : gamma, (forall temp. : term, (forall temp. : type, Type))) :="
        (first (string-split t "\n")))
      (check-regexp-match
        "T-Bla : (forall g : gamma, (forall e : term, (forall t : type, (meow g e t))))\\."
        (second (string-split t "\n"))))))
