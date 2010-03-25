AGDA=agda

test: Everything.agda
	$(AGDA) -i. -isrc README.agda

.PHONY: Everything.agda
Everything.agda:
	cabal install
	GenerateEverything
