# Top-level Makefile for Agda 2
# Author: Ulf Norell

## Includes ###############################################################

TOP = .

include mk/config.mk
include mk/paths.mk

## Phony targets ##########################################################

.PHONY : default all clean install full core debug doc dist

## Default target #########################################################

default : full

## Making the make system #################################################

m4_macros	= $(wildcard $(MACRO_DIR)/*.m4)

configure : aclocal.m4 configure.ac
	autoconf

aclocal.m4 : $(m4_macros)
	aclocal -I $(MACRO_DIR)

## Making the documentation ###############################################

doc :
	$(MAKE) -C $(HADDOCK_DIR)

## Making the full language ###############################################

full :
	$(MAKE) -C $(FULL_SRC_DIR)

## Making the core language ###############################################

core :
	$(MAKE) -C $(CORE_SRC_DIR)

## Making the source distribution #########################################

ifeq ($(HAVE_DARCS),Yes)
ifeq ($(shell if test -d _darcs; then echo darcs; fi),darcs)
  is_darcs_repo = Yes
else
  is_darcs_repo = No
endif
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

## Clean ##################################################################

clean :
	$(MAKE) -C $(FULL_SRC_DIR) clean
	$(MAKE) -C $(CORE_SRC_DIR) clean
	$(MAKE) -C $(HADDOCK_DIR) clean
	rm -rf $(OUT_DIR)

veryclean :
	$(MAKE) -C $(FULL_SRC_DIR) veryclean
	$(MAKE) -C $(CORE_SRC_DIR) veryclean
	$(MAKE) -C $(HADDOCK_DIR) veryclean
	rm -rf $(OUT_DIR)
	rm -rf configure config.log config.status aclocal.m4 autom4te.cache

## Debugging the Makefile #################################################

debug :
	@echo "Do we have ghc 6.4?            $(HAVE_GHC_6_4)"
	@echo "Is this the darcs repository?  $(is_darcs_repo)"
