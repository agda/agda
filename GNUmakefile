AGDA=agda

test: Everything.agda
	$(AGDA) -i. -isrc README.agda

setup: Everything.agda agda-lib-ffi

.PHONY: Everything.agda
Everything.agda:
	cabal install
	GenerateEverything

.PHONY: agda-lib-ffi
agda-lib-ffi:
	cd ffi && cabal install
