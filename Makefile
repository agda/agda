# Top-level Makefile for Agda 2
# Author: Ulf Norell

## Includes ###############################################################

TOP = .

is_configured = $(shell if test -f mk/config.mk; \
						then echo Yes; \
						else echo No; \
						fi \
				 )

ifeq ($(is_configured),Yes)
include mk/config.mk
endif
include mk/paths.mk


## Phony targets ##########################################################

.PHONY : default all clean install full prof core \
		 debug doc dist make_configure clean_test

## Default target #########################################################

ifeq ($(is_configured),Yes)
default : full core
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

full :
	$(MAKE) -C $(FULL_SRC_DIR)

prof :
	$(MAKE) -C $(FULL_SRC_DIR) prof

## Making the core language ###############################################

core :
	$(MAKE) -C $(CORE_SRC_DIR)

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

## Test ###################################################################

agda = $(FULL_OUT_DIR)/agda

# test_files	= $(patsubst %,examples/syntax/%,Syntax.agda Literate.lagda)

test_files = examples/Vec.agda test/simple.agda examples/bag.agda examples/Setoid.agda
tests	   = $(patsubst %,%.test,$(test_files))

# clean_test :
# 	@rm -f $(intermediate_files)

test : $(agda) $(tests)

$(tests) : %.test : %
	@echo "Testing $<..."
	@echo :q | $(agda) $<

## Clean ##################################################################

clean :
	$(MAKE) -C $(HADDOCK_DIR) clean
	rm -rf $(OUT_DIR)

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

