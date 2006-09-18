
mixfix : MixFix.hs
	ghc -o $@ --make $< -prof -auto-all -i../../full -odir . -hidir .

p=-p -hb

prof : mixfix
	time ./mixfix +RTS $(p)
	hp2ps -c mixfix.hp

