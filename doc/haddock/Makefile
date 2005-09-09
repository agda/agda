# Making the haddock documentation
# Author: Ulf Norell

## Includes ###############################################################

TOP = ../..

include $(TOP)/mk/config.mk
include $(TOP)/mk/paths.mk

## Variables ##############################################################

# Haddock base file
haddockBaseURL	= http://www.haskell.org/ghc/docs/latest/html/libraries/base
haddockBase		= $(haddockBaseURL),base.haddock
haddockBaseFile = $(haddockBaseURL)/base.haddock

# Haskell files
src_hs_files	= $(shell find $(FULL_SRC_DIR) -name '*.hs' -o '*.lhs')
dst_hs_files	= $(patsubst $(FULL_SRC_DIR)/%,src/%,$(hs_files))

# The prologue. Contains an introduction to the documentation
prologue		= prologue

## Phony targets ##########################################################

.PHONY : default clean veryclean

## Default target #########################################################

default : index.html

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
# directives in Haskell code, so we have to preprocess the source files
# before giving them to haddock. The preprocessing is done in two steps:
# first ghc's preprocessor is run, possibly calling the C preprocessor,
# and second all lines containing {-# SOURCE #-} are removed. This will 
# mean that types imported from boot files will not get linked to properly.
# A solution is to do the following (assuming the type X is imported from
# a boot file of module Foo):

# {- {-# SOURCE #-}
# -- | Trick to make haddock accept circular module dependencies. See 'Foo.X'.
# data X
# -}

# There is no need to do this for functions since they cannot appear in
# types, and thus not in haddock documentation.

src/% : $(FULL_SRC_DIR)/%
	@echo Preprocessing $* for Haddock
	@mkdir -p $(dir $@)
	@ghc -E -o $@.tmp $<
	@sed -e 's/.*{-# *SOURCE *#-}.*//;s/^#.*//' $@.tmp > $@
	@rm $@.tmp

## Building the haddock documentation #####################################

index.html : $(prologue) base.haddock $(dst_hs_files)
	$(HADDOCK) --odir=. --html --read-interface=$(haddockBase) \
							   --prologue=$(prologue) \
							   $(dst_hs_files)

## Clean ##################################################################

clean :
	rm -rf $(wildcard *.html) src haddock.css haskell_icon.gif

veryclean : clean
	rm -f base.haddock

