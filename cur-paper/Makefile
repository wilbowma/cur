RM=rm
SCRIBBLE=scribble

.PHONY: all clean distclean

all: /tmp/extended-abstract.pdf /tmp/main.pdf /tmp/abstract.md

/tmp/extended-abstract.pdf: abstract.scrbl extended-abstract.scrbl bib.rkt bib.bib defs.rkt smaller.tex
	$(SCRIBBLE) --dest /tmp --pdf extended-abstract.scrbl

/tmp/main.pdf: ../cur-lib/cur/curnel/model/*.rkt cur.rkt main.scrbl bib.rkt bib.bib defs.rkt abstract.scrbl intro.scrbl curnel.scrbl cur.scrbl syntax-sugar.scrbl related.scrbl smaller.tex tactics.scrbl olly.scrbl
	$(SCRIBBLE) ++style smaller.tex --dest /tmp --pdf main.scrbl
# dvipdf fails on OS X

/tmp/abstract.md: abstract.scrbl
	$(SCRIBBLE) --dest /tmp --markdown abstract.scrbl

clean:
	$(RM) -rf /tmp/retex-cache

distclean: clean
	$(RM) /tmp/main.pdf
