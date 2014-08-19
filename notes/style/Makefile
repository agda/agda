# Makefile Fun SS 2012

destdir=$(HOME)/public_html
bibliography=medium.bib

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'sort = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { url }'
catcfg=sed -e "s/%.*//g" <

latex=latex
pdflatex=pdflatex
lhs2tex=lhs2TeX --verbatim-comments

.PHONY : default debugMake

.PRECIOUS : %.dvi %.pdf %.tex

default : haskell-style.pdf

# # haskell-style
# ##################################################################

# # initially, run latex once to create an .aux file
# # mark .aux file as fresh by creating a stamp _aux
# haskell-style_aux : haskell-style.tex
# 	-$(latex) haskell-style.tex;
# 	touch $@;

# # then, run bibtex
# haskell-style.bbl : haskell-style_aux auto-haskell-style.bib
# 	-bibtex haskell-style;

# # finally, finish by running latex twice again
# # this will update .aux, but leave the stamp _aux intact
# # (otherwise we would not converge and make would never
# # return a "Nothing to do")
# haskell-style.dvi : haskell-style.bbl
# 	-$(latex) haskell-style.tex;
# 	-$(latex) haskell-style.tex;

# haskell-style.pdf : haskell-style.dvi
# 	$(pdflatex) haskell-style.tex

# ## pdflatex does not work since we are including a .ps file
# #haskell-style.pdf : haskell-style.bbl
# #	pdflatex haskell-style.tex;
# #	pdflatex haskell-style.tex;

# # auto-haskell-style.bib is only defined if bibtool is present and all.bib exists

# ifneq ($(shell which bibtool),)
# ifneq ($(shell ls $(bibliography)),)
# auto-haskell-style.bib : haskell-style_aux $(bibliography)
# 	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
# 	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
# 	echo "" >> $@ ;
# 	$(bibtool) -x haskell-style.aux -i $(bibliography) >> $@;
# endif
# endif

# Templates

%.tex : %.lagda
	lhs2TeX --agda $< > $@

%.tex : %.lhs
	$(lhs2tex) $< > $@

% : %.pdf
	cp -p $? $(destdir)/;
	touch $@;

%.dvi : %.tex
	$(latex) $<;
	-bibtex $*;
	$(latex) $<;
	$(latex) $<;

%.pdf : %.tex
	-pdflatex $*.tex;
	pdflatex $*.tex;

%.ps  : %.dvi
	dvips -o $@ $<;

%.gz : %
	cat $< | gzip > $@

clean :
	-rm *.aux *.log *.out *.ptb haskell-style.tex haskell-style.pdf

#EOF
