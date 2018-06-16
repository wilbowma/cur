#lang racket/base

(require data/bit-vector)
(provide (all-defined-out))

(define (ascii-char? c)
  (< (char->integer c) 127))

(define (ascii-string? str)
  (andmap ascii-char? (string->list str)))

(define (byte->ascii-bit-vector b)
  (bit-vector
   (bitwise-bit-set? b 6)
   (bitwise-bit-set? b 5)
   (bitwise-bit-set? b 4)
   (bitwise-bit-set? b 3)
   (bitwise-bit-set? b 2)
   (bitwise-bit-set? b 1)
   (bitwise-bit-set? b 0)))

(define (ascii-bit-vector->byte bv)
  (bitwise-ior
   (if (bit-vector-ref bv 6)
       1
       0)
   (if (bit-vector-ref bv 5)
       2
       0)
   (if (bit-vector-ref bv 4)
       4
       0)
   (if (bit-vector-ref bv 3)
       8
       0)
   (if (bit-vector-ref bv 2)
       16 
       0)
   (if (bit-vector-ref bv 1)
       32 
       0)
   (if (bit-vector-ref bv 0)
       64
       0)))

(define (char->ascii-bit-vector c)
  (byte->ascii-bit-vector (bytes-ref (integer->integer-bytes (char->integer c) 2 #f) 0)))

(define (ascii-bit-vector->char bv)
  (integer->char (ascii-bit-vector->byte bv)))
