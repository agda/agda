
default : algorithm.ps

%.dvi : %.tex
	latex $<
	latex $<

%.ps : %.dvi
	dvips -o $@ $<

