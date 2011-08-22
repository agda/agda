
%/Lex.x : %.cf
	bnfc -d $<

%/Par.y : %.cf
	bnfc -d $<

%.hs : %.x
	alex $<

%.hs : %.y
	happy -ihappy.out $<

Main : Syntax/Lex.hs Syntax/Par.hs $(shell find . -name '*.hs')
	ghc --make -O2 Main.hs -fwarn-incomplete-patterns

