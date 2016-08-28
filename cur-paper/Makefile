RM = /bin/rm
SCRIBBLE = scribble
OUTPUT_DIR ?= .

.PHONY: all clean distclean

all: $(OUTPUT_DIR)/extended-abstract.pdf $(OUTPUT_DIR)/main.pdf $(OUTPUT_DIR)/abstract.md

$(OUTPUT_DIR)/extended-abstract.pdf: abstract.scrbl extended-abstract.scrbl bib.rkt bib.bib defs.rkt smaller.tex
	$(SCRIBBLE) --dest $(OUTPUT_DIR) --pdf extended-abstract.scrbl

$(OUTPUT_DIR)/main.pdf: ../cur-lib/cur/curnel/model/*.rkt cur.rkt main.scrbl bib.rkt bib.bib defs.rkt abstract.scrbl intro.scrbl curnel.scrbl cur.scrbl syntax-sugar.scrbl related.scrbl smaller.tex tactics.scrbl olly.scrbl
	$(SCRIBBLE) ++style smaller.tex --dest $(OUTPUT_DIR) --pdf main.scrbl
# dvipdf fails on OS X

$(OUTPUT_DIR)/abstract.md: abstract.scrbl
	$(SCRIBBLE) --dest $(OUTPUT_DIR) --markdown abstract.scrbl

clean:
	$(RM) -rf $(OUTPUT_DIR)/retex-cache

distclean: clean
	$(RM) $(OUTPUT_DIR)/main.pdf
