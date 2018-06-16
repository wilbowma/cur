#lang s-exp "../main.rkt"

(require
 "datum.rkt"
 "sugar.rkt"
 "bool.rkt"
 "list.rkt")

(provide Ascii ascii Ascii-Str
         empty-ascii-str
         ascii-str-concat
         ascii-str-length
         build-ascii-string
         #%datum
         (rename-out
          [Ascii-Str AStr]
          [empty-ascii-str empty-astr]
          [ascii-str-concat astr-concat]
          [ascii-str-length astr-length]
          [build-ascii-string build-astr]))

(data Ascii : 0 Type
  (ascii : (-> Bool Bool Bool Bool Bool Bool Bool Ascii)))

(define Ascii-Str (List Ascii))
(define empty-ascii-str (nil Ascii))
(define ascii-str-concat (list-append Ascii))
(define ascii-str-length (length Ascii))
(define-syntax (build-ascii-string syn)
  (syntax-case syn ()
    [(_ e ...)
     #'(build-list Ascii e ...)]))

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


