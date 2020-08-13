# Agda version.
# This is incremented via the script src/release-tools/change-version.bash
VERSION=2.6.2

# GHC version removing the patchlevel number (e.g. in GHC 7.10.3, the
# patchlevel number is 3).

# We ask if GHC is available for removing a warning on Travis when
# testing the documentation.
ifneq ($(shell which ghc),)
GHC_VERSION := $(shell ghc --numeric-version | cut -d. -f1-2)
endif
