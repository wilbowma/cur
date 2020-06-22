#lang racket/base
(require
 (for-syntax
  racket/base
  "../curnel/reflection.rkt"))

(begin-for-syntax
  (require racket/trace)
  (current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map (compose curnel->datum cur-reflect) l) kw l2 n))))
  (current-trace-print-results
   (let ([ctpr (current-trace-print-results)])
     (lambda (s l n)
       (ctpr s (map (compose curnel->datum cur-reflect) l) n)))))
