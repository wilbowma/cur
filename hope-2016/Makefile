OUTPUT_DIR ?= .

.PHONY: all

all: $(OUTPUT_DIR)/figures.pdf $(OUTPUT_DIR)/figures-coq.html $(OUTPUT_DIR)/figures-rkt.html

$(OUTPUT_DIR)/figures.pdf: figures.tex mttex.sty
	latexmk -auxdir=$(OUTPUT_DIR) -outdir=$(OUTPUT_DIR) -pdf figures.tex

$(OUTPUT_DIR)/figures-coq.html: figures.v
	pygmentize -O full,style=emacs -f html -o $(OUTPUT_DIR)/figures-coq.html figures.v

$(OUTPUT_DIR)/figures-rkt.html: figures.rkt
	pygmentize -O full,style=emacs -f html -o $(OUTPUT_DIR)/figures-rkt.html figures.rkt

mttex:
	git submodule update --init

mttex.sty: mttex unlist.sty
	ln -s mttex/mttex.sty .

unlist.sty: mttex
	ln -s mttex/unlist.sty .
