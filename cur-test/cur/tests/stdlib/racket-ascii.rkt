#lang racket/base

(require
 cur/stdlib/racket-ascii
 data/bit-vector
 chk)

(chk
 #:t (ascii-char? #\A)
 #:t (ascii-char? #\a)
 #:t (ascii-char? (integer->char 126))
 #:! #:t (ascii-char? #\ö)
 #:! #:t (ascii-char? (integer->char 127)))

(chk
 #:t (ascii-string? "meow")
 #:t (ascii-string? "Hello, world!")
 #:! #:t (ascii-string? "Hello, wörld!"))

(chk
 #:= (ascii-bit-vector->byte (string->bit-vector "0000000")) 0
 #:= (ascii-bit-vector->byte (string->bit-vector "0000001")) 1
 #:= (ascii-bit-vector->byte (string->bit-vector "0001111")) 15
 #:= (ascii-bit-vector->byte (string->bit-vector "0001010")) 10
 #:= (ascii-bit-vector->byte (byte->ascii-bit-vector 10)) 10
 #:= (ascii-bit-vector->byte (byte->ascii-bit-vector 0)) 0
 #:= (ascii-bit-vector->byte (byte->ascii-bit-vector -1)) 127)

(chk
 #:= (char->integer #\!) 33
 #:= (char->integer #\1) 49
 #:= (bit-vector->string (char->ascii-bit-vector #\!)) "0100001"
 #:= (bit-vector->string (char->ascii-bit-vector #\1)) "0110001")
