# Making the haddock documentation
# Author: Ulf Norell

## Includes ###############################################################

TOP = ../..

include $(TOP)/mk/config.mk
include $(TOP)/mk/paths.mk

## Variables ##############################################################

# Haddock interface for the base package
haddockURL	= http://www.haskell.org/ghc/docs/$(GHC_VERSION)/html/libraries
haddockArg	= $(haddockURL)/$(1),$(1).haddock
haddockFile = $(haddockURL)/$(1)/$(1).haddock

# Haskell files
lexer			= Syntax/Parser/Lexer
parser			= Syntax/Parser/Parser
gen_hs_files	= $(FULL_OUT_DIR)/$(lexer).hs $(FULL_OUT_DIR)/$(parser).hs
src_hs_files	= $(shell $(FIND) $(FULL_SRC_DIR) -name '*.hs' -o -name '*.lhs')
dst_hs_files	= $(patsubst $(FULL_SRC_DIR)/%,src/%,$(src_hs_files)) \
				  $(patsubst $(FULL_OUT_DIR)/%,src/%,$(gen_hs_files))

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

%.haddock :
	wget $(call haddockFile,$*)

else

%.haddock :
	@echo $(call haddockFile,$*) have to be downloaded manually since wget could not be found.
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
	@$(MKDIR) -p $(dir $@)
	@$(GHC) -E -optP-P -optP-I$(FULL_SRC_DIR) -D__HADDOCK__ -o $@ $<

src/% : $(FULL_OUT_DIR)/% src
	@echo Preprocessing $* for haddock
	@$(MKDIR) -p $(dir $@)
	@$(GHC) -E -optP-P -optP-I$(FULL_SRC_DIR) -D__HADDOCK__ -o $@ $<

src :
	$(MKDIR) -p src

$(FULL_OUT_DIR)/$(parser).hs : $(FULL_SRC_DIR)/$(parser).y
	@$(MAKE) -C $(FULL_SRC_DIR) $@

$(FULL_OUT_DIR)/$(lexer).hs : $(FULL_SRC_DIR)/$(lexer).x
	@$(MAKE) -C $(FULL_SRC_DIR) $@

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

index.html : $(prologue) $(dst_hs_files) base.haddock mtl.haddock check_version 
	$(HADDOCK) --odir=. --html \
			--prologue=$(prologue) \
			--title="Agda II Documentation" \
			--ignore-all-exports \
			--read-interface=$(call haddockArg,base) \
			--read-interface=$(call haddockArg,mtl) \
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

