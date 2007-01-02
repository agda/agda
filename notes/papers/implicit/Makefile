
default : implicit.pdf

implicit.ps implicit.dvi implicit.pdf : $(wildcard *.tex) examples.tex exintro.tex lhs2TeXpreamble.tex

ifeq ($(shell which latexmk),)

%.dvi : %.tex
	latex --interaction=nonstopmode $<
	latex --interaction=nonstopmode $<

%.pdf : %.tex
	pdflatex $<

%.ps : %.dvi
	dvips -o $@ $<

else

%.pdf : %.tex
	latexmk -pdf $<

%.ps : %.tex
	latexmk -ps $<

endif

%.tex : %.lhs
	lhs2TeX --poly $< > $@

always :
	while true; do $(MAKE) implicit.ps; sleep 1; done | grep -v "^make"

