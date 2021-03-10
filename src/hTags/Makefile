
sources = $(shell find . -name '*hs')
bin			= dist/build/hTags/hTags
setup		= dist/setup-config

include ../../mk/cabal.mk

.PHONY : default

default : $(bin)

$(setup) : hTags.cabal
	$(CABAL) $(CABAL_OLD_INSTALL_CMD) --only-dependencies
	$(CABAL) $(CABAL_OLD_CONFIGURE_CMD)

$(bin) : $(setup) $(sources)
	$(CABAL) $(CABAL_OLD_BUILD_CMD)

