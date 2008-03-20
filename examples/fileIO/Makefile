
all : Base.hs IO.hs Main.hs IO/File.hs
	ghc --make Main.hs

%.hs : %.agda
	agda -c $<

