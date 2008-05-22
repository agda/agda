# Top-level Makefile for Agda 2
# Author: Ulf Norell

## Includes ###############################################################

TOP = .

is_configured = $(shell if test -f mk/config.mk; \
						then echo Yes; \
						else echo No; \
						fi \
				 )

include mk/paths.mk

ifeq ($(is_configured),Yes)
include mk/config.mk
include mk/rules.mk
endif


## Phony targets ##########################################################

.PHONY : default all clean install full prof core \
		 debug doc dist make_configure clean_test examples \
		 test succeed fail benchmark

## Default target #########################################################

ifeq ($(is_configured),Yes)
default : full core transl tags
else
default : make_configure
endif

## Making the make system #################################################

m4_macros	= $(wildcard $(MACRO_DIR)/*.m4)

make_configure : configure
	@echo "Run './configure' to set up the build system."

configure : aclocal.m4 $(m4_macros) configure.ac
	autoconf

##
## The following targets are only available after running configure #######
##

ifeq ($(is_configured),Yes)

## Making the documentation ###############################################

doc :
	$(MAKE) -C $(HADDOCK_DIR)

## Making the full language ###############################################

ifeq ($(HAVE_RUNHASKELL),Yes)

SETUP	   = Setup.hs
RUNSETUP   = $(RUNHASKELL) $(SETUP)

else

SETUP	   = setup
RUNSETUP   = ./setup

$(SETUP) : Setup.hs
	ghc --make -o $@ $<

endif

CONFIG	= dist/setup-config
CABAL		= Agda.cabal
BUILD		= dist/build-complete
INPLACE = dist/installed-inplace
SOURCES = $(shell $(FIND) $(FULL_SRC_DIR) -name '*hs') \
					$(shell $(FIND) $(FULL_SRC_DIR) -name '*.y') \
					$(shell $(FIND) $(FULL_SRC_DIR) -name '*.x')

$(CONFIG) : $(CABAL) $(SETUP)
	$(RUNSETUP) configure

$(BUILD) : $(CONFIG) $(SOURCES)
	$(RUNSETUP) build
	@date > $@

$(INPLACE) : $(BUILD)
	$(RUNSETUP) register --user --inplace
	@date > $@

$(AGDA_BIN) : $(INPLACE) $(MAIN_SRC_DIR)/Main.hs
	$(MAKE) -C $(MAIN_SRC_DIR)

full : $(AGDA_BIN)

prof :
	$(MAKE) -C $(MAIN_SRC_DIR) prof

## Making the core language ###############################################

core :
	$(MAKE) -C $(CORE_SRC_DIR)

## Making the Agda 1 to Agda 2 translator #################################

transl :
	(cd $(TRANSL_SRC_DIR); $(RUNSETUP) build)

## Making the source distribution #########################################

ifeq ($(HAVE_DARCS)-$(shell if test -d _darcs; then echo darcs; fi),Yes-darcs)
  is_darcs_repo = Yes
else
  is_darcs_repo = No
endif

ifeq ($(is_darcs_repo),Yes)

dist : agda2.tar.gz

agda2.tar.gz :
	$(DARCS) dist -d agda2

else

dist :
	@echo You can only "'make dist'" from the darcs repository.
	@$(FALSE)

endif

ifeq ($(HAVE_HASKTAGS),Yes)
tags :
	$(MAKE) -C $(FULL_SRC_DIR) tags
else
tags :
	@true
endif

## Testing ###########################################################

test : succeed examples fail tests library-test

tests :
	@echo "======================================================================"
	@echo "======================== Internal test suite ========================="
	@echo "======================================================================"
	$(AGDA_BIN) --test

succeed : 
	@echo "======================================================================"
	@echo "===================== Suite of successfull tests ====================="
	@echo "======================================================================"
	@$(MAKE) -C test/succeed 

examples :
	@echo "======================================================================"
	@echo "========================= Suite of examples =========================="
	@echo "======================================================================"
	@$(MAKE) -C examples

fail :
	@echo "======================================================================"
	@echo "======================= Suite of failing tests ======================="
	@echo "======================================================================"
	@$(MAKE) -C test/fail

library-test :
	@echo "======================================================================"
	@echo "========================== Standard library =========================="
	@echo "======================================================================"
	@DIR=`mktemp -dt` && \
	  (darcs get --partial --repo-name=$$DIR/lib \
		 http://www.cs.nott.ac.uk/~nad/repos/lib/ && \
	   $(AGDA_BIN) -i$$DIR/lib $$DIR/lib/Everything.agda); \
	  RETURN_VALUE=$$?; rm -rf $$DIR && [ $$RETURN_VALUE = 0 ]

benchmark :
	@$(MAKE) -C benchmark

## Clean ##################################################################

clean :
	$(MAKE) -C $(HADDOCK_DIR) clean
	rm -rf $(OUT_DIR)
	rm -rf dist

veryclean :
	$(MAKE) -C $(HADDOCK_DIR) veryclean
	rm -rf $(OUT_DIR)
	rm -rf configure config.log config.status autom4te.cache mk/config.mk

## Debugging the Makefile #################################################

info :
	@echo "Do we have ghc 6.4?            $(HAVE_GHC_6_4)"
	@echo "Is this the darcs repository?  $(is_darcs_repo)"

else	# is_configured

info :
	@echo "You haven't run configure."

endif	# is_configured

