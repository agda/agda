
CABAL_CMD=cabal

CABAL_VERSION := $(shell $(CABAL_CMD) --numeric-version | cut -d. -f1-2)

# Amazing hack to do =< comparison (due to https://stackoverflow.com/questions/3437160).
# Relies on there being no cabal 2.10.x or above.
ifeq ("2.4","$(word 1,$(sort 2.4 $(CABAL_VERSION)))")
	CABAL_BUILD_CMD=v1-build
	CABAL_CLEAN_CMD=v1-clean
	CABAL_CONFIGURE_CMD=v1-configure
	CABAL_HADDOCK_CMD=v1-haddock
	CABAL_INSTALL_CMD=v1-install
	CABAL_OLD_BUILD_CMD=$(CABAL_BUILD_CMD)
	CABAL_OLD_INSTALL_CMD=$(CABAL_INSTALL_CMD)
	CABAL_OLD_CONFIGURE_CMD=$(CABAL_CONFIGURE_CMD)
else
	CABAL_BUILD_CMD=build
	CABAL_CLEAN_CMD=clean
	CABAL_CONFIGURE_CMD=configure
	CABAL_HADDOCK_CMD=haddock
	CABAL_INSTALL_CMD=install
	CABAL_OLD_BUILD_CMD=$(CABAL_BUILD_CMD)
	CABAL_OLD_INSTALL_CMD=$(CABAL_INSTALL_CMD)
	CABAL_OLD_CONFIGURE_CMD=$(CABAL_CONFIGURE_CMD)
endif
