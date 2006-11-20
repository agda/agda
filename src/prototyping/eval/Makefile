
default : eval_p

srcs = $(shell find . -name '*.hs') Lam/Par.hs Lam/Lex.hs

flags   = -O -fwarn-incomplete-patterns -Werror
flags_p = -odir prof -hidir prof -prof -auto-all

eval : $(srcs)
	ghc --make Main -o $@ $(flags)

eval_p : prof $(srcs)
	ghc -O --make Main -o $@ $(flags) $(flags_p)

prof :
	mkdir prof

%/Par.y %/Lex.x : %.cf
	bnfc -d $<

%.hs : %.y
	happy -agci $<

%.hs : %.x
	alex $<

%.ps : %.hp
	hp2ps -c $<

n = dbLazy7
p = -Pa

%.hp %.prof : % .dummy
	./$< nat.lam -n $n +RTS $p
	@rm .dummy

.dummy :
	@touch .dummy

