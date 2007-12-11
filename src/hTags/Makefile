
sources = $(shell find . -name '*hs')
bin			= dist/build/hTags/hTags
setup		= dist/setup-config

.PHONY : default

default : $(bin)

$(setup) : hTags.cabal
	runhaskell Setup.hs configure

$(bin) : $(setup) $(sources)
	runhaskell Setup.hs build

