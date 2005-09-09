# Making the haddock documentation
# Author: Ulf Norell

## Includes ###############################################################

TOP = ../..

include $(TOP)/mk/config.mk
include $(TOP)/mk/paths.mk

## Variables ##############################################################

# Haddock interface for the base package
haddockBaseURL	= http://www.haskell.org/ghc/docs/$(GHC_VERSION)/html/libraries/base
haddockBase		= $(haddockBaseURL),base.haddock
haddockBaseFile = $(haddockBaseURL)/base.haddock

# Haskell files
src_hs_files	= $(shell $(FIND) $(FULL_SRC_DIR) -name '*.hs' -o -name '*.lhs')
dst_hs_files	= $(patsubst $(FULL_SRC_DIR)/%,src/%,$(src_hs_files))

# The prologue. Contains an introduction to the documentation
prologue		= prologue

## Phony targets ##########################################################

.PHONY : default clean veryclean debug check_version

## Default target #########################################################

ifeq ($(HAVE_HADDOCK),Yes)

default : index.html

else

default :
	@echo You need haddock to build this documentation.
	@$(FALSE)

endif

## Base file ##############################################################

ifeq ($(HAVE_WGET),Yes)

base.haddock :
	wget $(haddockBaseFile)

else

base.haddock :
	@echo $(haddockBaseFile) have to be downloaded manually since wget could not be found.
	@$(FALSE)

endif

## Preprocessing Haskell files ############################################

# Haddock cannot handle circular module dependencies or C preprocessor
# directives in Haskell code, so we have to let ghc preprocess the source
# files before giving them to haddock. To handle circular module
# dependencies surround the boot file imports with an
# #ifndef __HADDOCK__
# It might also be necessary to define a dummy version of types imported
# from boot files as follows:

# #ifndef __HADDOCK__
# import Foo (X)
# #endif
# ...
# #ifdef __HADDOCK__
# -- | Trick to make haddock accept circular module dependencies. See 'Foo.X'.
# data X
# #endif

# There is no need to do this for functions since they cannot appear in
# types, and thus not in haddock documentation.

src/% : $(FULL_SRC_DIR)/% src
	@echo Preprocessing $* for haddock
	@mkdir -p $(dir $@)
	@ghc -E -D__HADDOCK__ -o $@ $<

src :
	mkdir -p src

## Building the haddock documentation #####################################

# It would be nice to check which version of haddock the ghc library
# documentation is built with, but I don't know how (in an easy way).
# For now it's hard-wired.
ifeq ($(HAVE_GHC_6_4),Yes)
base_interface_version = 0.7
else
base_interface_version = 0.6
endif

ifeq ($(HADDOCK_VERSION),$(base_interface_version))
check_version :
else
check_version :
	@echo "Warning: The ghc library documentation was probably"
	@echo "         built using version $(base_interface_version) of haddock, but you"
	@echo "         are using version $(HADDOCK_VERSION). Haddock might not be"
	@echo "         able to link to library definitions."
endif

# The naming convention in haddock has changed from . to - for
# hierarchical modules, but the standard library documentation
# still uses . so the links are all wrong. Better not link at all.
# base.haddock check_version 
#			--read-interface=$(haddockBase)
index.html : $(prologue) $(dst_hs_files)
	$(HADDOCK) --odir=. --html \
			--prologue=$(prologue) \
			--title="Agda II Documentation" \
			$(dst_hs_files)

## Clean ##################################################################

clean :
	rm -rf $(wildcard *.html) src haddock.css haskell_icon.gif

veryclean : clean
	rm -f base.haddock

## Debugging the Makefile #################################################

debug :
	@echo The Haskell sources are
	@echo "  $(src_hs_files)"
	@echo The preprocessed files are
	@echo "  $(dst_hs_files)"

