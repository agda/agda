
default : talk.ps

modules.pdf : talk.tex
	latexmk -pdf talk.tex
	pdfnup --noautoscale true --nup 1x1 --orient landscape talk.pdf --scale 2.1 --outfile $@

%.ps : %.tex
	latexmk -ps $<

%.tex : %.lhs
	lhs2TeX --poly $< > $@

always :
	while true; do $(MAKE) default; sleep 1; done | grep -v "^make"

