AGDA=agda

test: Everything.agda
	fix-agda-whitespace --check
	$(AGDA) -i. -isrc README.agda

setup: Everything.agda agda-lib-ffi

.PHONY: Everything.agda
Everything.agda:
	cabal install
	GenerateEverything

.PHONY: agda-lib-ffi
agda-lib-ffi:
	cd ffi && cabal install

.PHONY: listings
listings: Everything.agda
	$(AGDA) -i. -isrc --html README.agda -v0

