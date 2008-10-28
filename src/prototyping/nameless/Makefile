
default : nameless

srcs = $(shell find . -name '*.hs') Lam/Par.hs Lam/Lex.hs

flags   = -O -fwarn-incomplete-patterns -Werror

nameless : $(srcs)
	ghc --make Main -o $@ $(flags)

%/Par.y %/Lex.x : %.cf
	bnfc -d $<

%.hs : %.y
	happy -agc -i$*.info $<

%.hs : %.x
	alex $<

clean :
	@rm -rf *.hi *.o Lam nameless

