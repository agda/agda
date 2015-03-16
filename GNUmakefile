AGDA=agda

test: Everything.agda
# We don't have the `fix-agda-whitespace` command on Travis, so we
# ignore the error using `-`.
	-fix-agda-whitespace --check
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

