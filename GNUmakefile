AGDA=agda

test: Everything.agda
	fix-agda-whitespace --check
	$(AGDA) -i. -isrc README.agda

setup: Everything.agda agda-lib-ffi

.PHONY: Everything.agda
Everything.agda:
	cabal clean && cabal install
	GenerateEverything

.PHONY: agda-lib-ffi
agda-lib-ffi:
	cd ffi && cabal clean && cabal install

.PHONY: listings
listings: Everything.agda
	$(AGDA) -i. -isrc --html README.agda -v0

clean :
	find . -type f -name '*.agdai' -delete
