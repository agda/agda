
default : module

srcs = $(shell find . -name '*.hs') Syntax/Par.hs Syntax/Lex.hs

flags   = -fwarn-incomplete-patterns
flags_p = -odir prof -hidir prof -prof -auto-all

module : $(srcs)
	ghc --make Main -o $@ $(flags)

%/Par.y %/Lex.x : %.cf
	bnfc -d $<

%.hs : %.y
	happy -agci $<

%.hs : %.x
	alex $<

