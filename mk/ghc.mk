include $(TOP)/mk/cabal.mk
include $(TOP)/mk/stack.mk

ifeq ($(GHC),)
  ifdef HAS_STACK
    GHC := stack ghc --
  else
    GHC := $(shell which ghc)
  endif
endif

ifeq ($(RUNGHC),)
  ifdef HAS_STACK
    RUNGHC := stack runghc --
  else
    RUNGHC := $(shell which runghc)
  endif
endif

# GHC version removing the patchlevel number (e.g. in GHC 7.10.3, the
# patchlevel number is 3).

# We ask if GHC is available for removing a warning on Travis when
# testing the documentation.
ifneq ($(GHC),)
GHC_VERSION := $(shell $(GHC) --numeric-version | cut -d. -f1-2)
endif
