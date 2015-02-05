cur
===

CIC under Racket. A language with static dependent-types and dynamic
types, type annotations and parentheses, theorem proving and
meta-programming.

```
Noun
cur (plural curs)

1. (archaic) A mongrel.
2. (archaic) A detestable person.
```

Getting started
===============

Don't actually try to run anything. The type-checker may be exponential,
or worse.

Open up `stlc.rkt` to see an example of what advanced meta-programming can let you do.

Open up `oll.rkt` to see the implementation of the meta-programs used to
enable `stlc.rkt`, including the parsers for BNF syntax, inference rule
relation syntax, and Coq and LaTeX generators.

Open up `proofs-for-free.rkt` to see an implementation of the
translation defined in [Proofs for Free](http://staff.city.ac.uk/~ross/papers/proofs.html) as a meta-program.

Open up anything in `stdlib/` to see some standard dependent-type
formalisms.
