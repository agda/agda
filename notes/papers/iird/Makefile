
default : paper.ps

paper.ps paper.dvi paper.pdf : macros.tex

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
	@while true; do $(MAKE) | grep -v "Nothing to be done" | grep -v "\(Leaving\|Entering\) directory"; sleep 1; done

