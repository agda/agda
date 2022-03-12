include $(TOP)/mk/cabal.mk
include $(TOP)/mk/stack.mk

ifeq ($(GHC),)
  ifdef HAS_STACK
    GHC := $(STACK_SILENT) ghc --
  else
    GHC := $(shell which ghc)
  endif
endif

ifeq ($(RUNGHC),)
  ifdef HAS_STACK
    RUNGHC := $(STACK_SILENT) runghc --
  else
    RUNGHC := $(shell which runghc)
  endif
endif

# GHC version removing the patchlevel number (e.g. in GHC 7.10.3, the
# patchlevel number is 3).

# We ask if GHC is available for removing a warning on Travis when
# testing the documentation.
ifneq ($(GHC),)

  # major.minor.subminor, e.g. 8.10.2
  ifdef HAS_STACK
    GHC_VER := $(shell $(STACK) query | sed -n 's/.*actual: ghc-\([0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\).*/\1/p')
    # The following variant needs GNU awk (not POSIX compatible) [issue #5480]:
    # GHC_VER := $(shell $(STACK) query | awk 'match ($$0, /actual: ghc-([0-9]+\.[0-9]+\.[0-9]+)/, ver) { print (ver[1]); }')
  else
    GHC_VER := $(shell $(GHC) --numeric-version | cut -d. -f1-3)
  endif

  # major.minor, e.g. 8.10
  #GHC_VERSION := $(shell echo $(GHC_VER) | cut -d. -f1-2)
  # ALT: `cut` can be done within `make`:
  # substitute dot by space, select words 1-2, substitute space by dot
  # Howeve, for the last substitution step, we need a hack to define
  # $(space) as leading spaces are ignored in the first argument to subst.
  # See https://www.gnu.org/software/make/manual/make.html#Text-Functions
  empty :=
  space := $(empty) $(empty)
  GHC_VERSION := $(subst $(space),.,$(wordlist 1,2,$(subst .,$(space),$(GHC_VER))))
endif
