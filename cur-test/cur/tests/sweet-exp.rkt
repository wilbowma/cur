#lang sweet-exp cur
require
 cur/stdlib/sugar
 cur/stdlib/bool
 cur/stdlib/nat
 rackunit

check-equal?
  if true false true
  false

define + plus

check-equal?
  {z + s(z)}
  s(z)
