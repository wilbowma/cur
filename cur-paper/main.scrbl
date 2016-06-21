#lang scribble/sigplan @preprint @nocopyright
@(require "defs.rkt" "bib.rkt")

@title{Growing a Proof Assistant}
@(authorinfo "William J. Bowman" "wjb@williamjbowman.com" "Northeastern University")

@include-abstract{abstract.scrbl}

@include-section{intro.scrbl}
@include-section{curnel.scrbl}
@include-section{cur.scrbl}
@include-section{syntax-sugar.scrbl}
@include-section{tactics.scrbl}
@include-section{olly.scrbl}

@include-section{related.scrbl}

@(generate-bibliography)
