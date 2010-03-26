
dist=dist

gen=Syntax/Skel Syntax/Par Syntax/Lex Syntax/Abs
gen_files=$(patsubst %,$(dist)/%.hs,$(gen))
src_files=$(wildcard *.hs)

term : $(gen_files) $(src_files)
	ghc --make Main -o $@ -i$(dist) -odir=$(dist) -hidir=$(dist)

$(dist)/%/Skel.hs $(dist)/%/Par.y $(dist)/%/Lex.x $(dist)/%/Abs.hs : %.cf
	bnfc -haskell -d $<
	-rm -rf $(dist)/$*
	mv $* $(dist)

%.hs : %.x
	alex $< -o $@

%.hs : %.y
	happy $< --info=$*.happy.out -o $@

