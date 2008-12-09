
sources = $(shell find . -name '*hs')
bin			= dist/build/hTags/hTags
setup		= dist/setup-config

.PHONY : default

default : $(bin)

$(setup) : hTags.cabal
	cabal configure

$(bin) : $(setup) $(sources)
	cabal build

