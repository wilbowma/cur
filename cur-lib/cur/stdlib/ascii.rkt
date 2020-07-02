#lang s-exp "../main.rkt"

(require
 "datum.rkt"
 "sugar.rkt"
 "bool.rkt"
 "list.rkt")

(provide Ascii ascii Ascii-Str (rename-out [Ascii-Str String])
         (for-syntax ~String)
         empty-ascii-str
         ascii-str-concat
         ascii-str-length
         build-ascii-string
         ascii-equal? string-equal?
         #%datum
         (rename-out
          [Ascii-Str AStr]
          [empty-ascii-str empty-astr]
          [ascii-str-concat astr-concat]
          [ascii-str-length astr-length]
          [build-ascii-string build-astr]))

(data Ascii : 0 Type
  (ascii : (-> Bool Bool Bool Bool Bool Bool Bool Ascii)))

(define-for-export Ascii-Str (List Ascii))
(define-for-export empty-ascii-str (nil Ascii))
(define-for-export ascii-str-concat (list-append Ascii))
(define-for-export ascii-str-length (length Ascii))
(define-syntax (build-ascii-string syn)
  (syntax-case syn ()
    [(_ e ...)
     #'(build-list Ascii e ...)]))

(begin-for-syntax
  (require (for-syntax racket/base syntax/parse))
  (define-syntax ~String
    (pattern-expander
     (syntax-parser
       [:id #'(~List ~Ascii)]
       [(_ . rst) #'((~List ~Ascii) . rst)]))))

(define/rec/match ascii-equal? : Ascii Ascii -> Bool
  [(ascii a1 a2 a3 a4 a5 a6 a7)
   (ascii b1 b2 b3 b4 b5 b6 b7) =>
   (and (bool-equal? a1 b1)
        (and (bool-equal? a2 b2)
             (and (bool-equal? a3 b3)
                  (and (bool-equal? a4 b4)
                       (and (bool-equal? a5 b5)
                            (and (bool-equal? a6 b6)
                                 (bool-equal? a7 b7)))))))])

(define/rec/match string-equal? : (List Ascii) (List Ascii) -> Bool
  [(nil _) (nil _) => true]
  [(nil _) (cons _ _ _) => false]
  [(cons _ _ _) (nil _) => false]
  [(cons _ a rsta) (cons _ b rstb) => (and (ascii-equal? a b)
                                           (string-equal? rsta rstb))])
;; this version makes it harder to prove beq-string-refl
#;(define (string-equal? [s1 : Ascii-Str] [s2 : Ascii-Str])
  (andmap2 Ascii Ascii ascii-equal? s1 s2))

(begin-for-syntax
  (require "racket-ascii.rkt" data/bit-vector racket/contract)
  (provide meta-ascii->ascii ascii->meta-ascii ascii-str->meta-string meta-string->ascii-str)

  (define (meta-ascii->ascii syn char)
    (unless (ascii-char? char)
      (raise-syntax-error
       'datum-error
       "I only know how to parse ASCII chars"
       syn))
    (define bv (char->ascii-bit-vector char))
    #`(ascii
       #,@(for/list ([b (in-bit-vector bv)])
            (meta-bool->bool b))))

  (define (meta-string->ascii-str syn str)
    (unless (ascii-string? str)
      (raise-syntax-error
       'datum-error
       "I only know how to parse ASCII string"
       syn))
    #`(build-ascii-string #,@(for/list ([str (in-string str)])
                               (meta-ascii->ascii #f str))))

  (define (ascii-datum syn f)
    (syntax-parse syn
      [s:str
       (meta-string->ascii-str syn (syntax->datum syn))]
      [_ (f syn)]))

  (current-datum ascii-datum)

  (define (ascii->meta-ascii syn)
    (syntax-parse syn
      #:literals (ascii true false)
      [(ascii bits ...)
       (ascii-bit-vector->char
        (for/bit-vector ([b (attribute bits)])
          (bool->meta-bool b)))]))

  (require (only-in racket/base [cons racket-cons]))
  (define (ascii-str->meta-string syn)
    (list->string
     (let astr->list ([syn syn])
        (syntax-parse syn
          #:literals (Ascii ascii cons nil)
          [(nil Ascii)
           '()]
          [(cons Ascii (ascii bits ...) rest)
           (racket-cons
            (ascii->meta-ascii #'(ascii bits ...))
            (astr->list #'rest))])))))


