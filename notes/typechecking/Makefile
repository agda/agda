
default : algorithm.ps

%.dvi : %.tex
	latex --interaction=nonstopmode $<
	latex --interaction=nonstopmode $<

%.ps : %.dvi
	dvips -o $@ $<

