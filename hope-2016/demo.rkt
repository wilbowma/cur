#lang cur

(require
 cur/stdlib/sugar
 cur/ntac/base
 cur/ntac/standard)

(ntac (forall (A : Type) (a : A) A)
      interactive)

