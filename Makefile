# Top-level Makefile for Agda 2
# Author: Ulf Norell

## Includes ###############################################################

TOP = .

include mk/config.mk
include mk/paths.mk

## Phony targets ##########################################################

.PHONY : default all clean install full core debug doc

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

## Debugging the Makefile #################################################

debug :
	@echo Do we have ghc 6.4? $(HAVE_GHC_6_4)
