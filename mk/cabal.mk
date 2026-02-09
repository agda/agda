
CABAL=cabal

CABAL_VERSION := $(shell $(CABAL) --numeric-version 2> /dev/null | cut -d. -f1-2)

CABAL_BUILD_CMD=v1-build
CABAL_CLEAN_CMD=v1-clean
CABAL_CONFIGURE_CMD=v1-configure
CABAL_HADDOCK_CMD=v1-haddock
CABAL_INSTALL_CMD=v1-install
