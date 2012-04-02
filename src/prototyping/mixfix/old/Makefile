
mixfix : MixFix.hs
	ghc -o $@ --make $< -prof -auto-all -i../../../full -odir . -hidir .

mixfix2 : MixFix2.hs
	ghc -O -o $@ --make $< -main-is $(<:.hs=.main) -i../../../full -odir . -hidir .

mixfixSlow : MixFix2.hs
	ghc -O -o $@ --make $< -main-is $(<:.hs=.slowMain) -i../../../full -odir . -hidir .

p=-p -hb

prof : mixfix
	time ./mixfix +RTS $(p)
	hp2ps -c mixfix.hp
