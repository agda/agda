
default : implicit.pdf

implicit.ps implicit.dvi implicit.pdf : $(wildcard *.tex)

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

