
default : algorithm.ps algorithm.pdf

%.dvi : %.tex
	latex --interaction=nonstopmode $<
	latex --interaction=nonstopmode $<

%.pdf : %.tex
	pdflatex $<

%.ps : %.dvi
	dvips -o $@ $<

