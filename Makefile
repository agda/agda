# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson

# Profiling verbosity for library-test
PROFVERB=7

SHELL=bash
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

## Default target #########################################################

.PHONY : default

ifeq ($(is_configured),Yes)
default : install-bin
# tags
else
default : make_configure
endif

## Cabal-based installation ###############################################

# The cabal command.
CABAL_CMD=cabal

CABAL_OPTS=$(CABAL_OPTIONS)

# Options used by cabal install.
CABAL_OPTS+=--builddir=dist/$(VERSION)
#  -f old-time
#  -f epic

# If you want to make use of parallel compilation with ghc>=7.8,
# enable the flag below, or set the "jobs" field in your
# ".cabal/config".
#
# ifeq ($(HAVE_GHC_7_7),Yes)
# CABAL_OPTS+=--ghc-option=-j3
# endif

.PHONY : install
install : install-bin compile-emacs-mode setup-emacs-mode

.PHONY : prof
prof : install-prof-bin

# Installs the Emacs mode, but does not set it up.
.PHONY : install-bin
install-bin :
	time $(CABAL_CMD) install --disable-library-profiling --disable-documentation $(CABAL_OPTS)

.PHONY : install-O0-bin
install-O0-bin :
	$(CABAL_CMD) install -O0 --disable-library-profiling --disable-documentation $(CABAL_OPTS)

.PHONY : install-O2-bin
install-O2-bin :
	$(CABAL_CMD) install -O2 --disable-library-profiling --disable-documentation $(CABAL_OPTS)

.PHONY : install-prof-bin
install-prof-bin :
	$(CABAL_CMD) install --enable-library-profiling --enable-executable-profiling \
                             --program-suffix=_p --disable-documentation $(CABAL_OPTS)

.PHONY : compile-emacs-mode
compile-emacs-mode : install-bin
	agda-mode compile

.PHONY : setup-emacs-mode
setup-emacs-mode : install-bin
	@echo
	@echo "If the agda-mode command is not found, make sure that the directory"
	@echo "in which it was installed is located on your shell's search path."
	@echo
	agda-mode setup

## Making the make system #################################################

m4_macros	= $(wildcard $(MACRO_DIR)/*.m4)

.PHONY : make_configure
make_configure : configure
	@echo "Run './configure' to set up the build system."

.PHONY : configure
configure : aclocal.m4 $(m4_macros) configure.ac
	autoconf

##
## The following targets are only available after running configure #######
##

ifeq ($(is_configured),Yes)

## Making the documentation ###############################################

.PHONY : doc
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

.PHONY : full
full : $(AGDA_BIN)

## Making the core language ###############################################

.PHONY : core
core :
	$(MAKE) -C $(CORE_SRC_DIR)

## Making the Agda 1 to Agda 2 translator #################################

.PHONY : transl
transl :
	(cd $(TRANSL_SRC_DIR); cabal configure && cabal build)

## Making the source distribution #########################################

ifeq ($(HAVE_DARCS)-$(shell if test -d _darcs; then echo darcs; fi),Yes-darcs)
  is_darcs_repo = Yes
else
  is_darcs_repo = No
endif

.PHONY : dist

ifeq ($(is_darcs_repo),Yes)

dist : agda2.tar.gz

agda2.tar.gz :
	$(DARCS) dist -d agda2

else

dist :
	@echo You can only "'make dist'" from the darcs repository.
	@$(FALSE)

endif

.PHONY : tags
tags :
	$(MAKE) -C $(FULL_SRC_DIR) tags

.PHONY : TAGS
TAGS :
	$(MAKE) -C $(FULL_SRC_DIR) TAGS

## Testing ###########################################################

.PHONY : quick
quick : install-O0-bin quicktest

.PHONY : test
test : check-whitespace succeed fail interaction latex-test examples library-test lib-succeed compiler-test epic-test api tests

.PHONY : quicktest
quicktest : succeed fail

.PHONY : tests
tests :
	@echo "======================================================================"
	@echo "======================== Internal test suite ========================="
	@echo "======================================================================"
	$(AGDA_BIN) --test +RTS -M1g

.PHONY : succeed
succeed :
	@echo "======================================================================"
	@echo "===================== Suite of successfull tests ====================="
	@echo "======================================================================"
	@chmod +x test/succeed/checkOutput
	@$(MAKE) -C test/succeed

.PHONY : interaction
interaction :
	@echo "======================================================================"
	@echo "===================== Suite of interaction tests ====================="
	@echo "======================================================================"
	@$(MAKE) -C test/interaction

.PHONY : examples
examples :
	@echo "======================================================================"
	@echo "========================= Suite of examples =========================="
	@echo "======================================================================"
	@$(MAKE) -C examples

.PHONY : fail
fail :
	@echo "======================================================================"
	@echo "======================= Suite of failing tests ======================="
	@echo "======================================================================"
	@$(MAKE) -C test/fail

.PHONY : latex-test
latex-test :
	@echo "======================================================================"
	@echo "================== Suite of tests for LaTeX backend =================="
	@echo "======================================================================"
	@$(MAKE) -C test/latex-backend clean
	@$(MAKE) -C test/latex-backend all
	@$(MAKE) -C test/latex-backend clean

.PHONY : std-lib
std-lib :
	if [ ! -d $@ ]; then \
	   git clone https://github.com/agda/agda-stdlib.git $@; \
	fi

.PHONY : up-to-date-std-lib
up-to-date-std-lib : std-lib
	@(cd std-lib && \
	  git fetch && git checkout master && git merge origin/master && \
	  make setup)

.PHONY : library-test
library-test : # up-to-date-std-lib
	@echo "======================================================================"
	@echo "========================== Standard library =========================="
	@echo "======================================================================"
	@(cd std-lib && \
          time $(PWD)/$(AGDA_BIN) -v profile:$(PROFVERB) -i. -isrc README.agda $(AGDA_TEST_FLAGS) \
            +RTS -s -H1G -M1.5G)

.PHONY : continue-library-test
continue-library-test :
	@(cd std-lib && \
          time $(PWD)/$(AGDA_BIN) -v profile:$(PROFVERB) -i. -isrc README.agda +RTS -s -H1G -M1.5G)

.PHONY : compiler-test
compiler-test : # up-to-date-std-lib
	@echo "======================================================================"
	@echo "============================== Compiler =============================="
	@echo "======================================================================"
	@$(MAKE) -C test/compiler

.PHONY : lib-succeed
lib-succeed :
	@echo "======================================================================"
	@echo "========== Successfull tests using the standard library =============="
	@echo "======================================================================"
	@$(MAKE) -C test/$@

.PHONY : epic-test
epic-test :
	@echo "======================================================================"
	@echo "============================ Epic backend ============================"
	@echo "======================================================================"
	@$(MAKE) -C test/epic

.PHONY : api
api :
	@echo "======================================================================"
	@echo "======== Successfull tests using Agda as an Haskell library =========="
	@echo "======================================================================"
	@$(MAKE) -C test/$@

.PHONY : benchmark
benchmark :
	@$(MAKE) -C benchmark

## Clean ##################################################################

.PHONY : clean
clean :
	$(MAKE) -C $(HADDOCK_DIR) clean
	rm -rf $(OUT_DIR)
	rm -rf dist

.PHONY : veryclean
veryclean :
	$(MAKE) -C $(HADDOCK_DIR) veryclean
	rm -rf $(OUT_DIR)
	rm -rf configure config.log config.status autom4te.cache mk/config.mk

## Debugging the Makefile #################################################
.PHONY : info

info :
	@echo "The agda binary is at:         $(AGDA_BIN)"
	@echo "Do we have ghc 7.7?            $(HAVE_GHC_7_7)"
	@echo "Is this the darcs repository?  $(is_darcs_repo)"
	@echo "Agda test flags are:           $(AGDA_TEST_FLAGS)"
	@echo "Cabal flags are:               $(CABAL_OPTS)"

else	# is_configured

info :
	@echo "You haven't run configure."

endif	# is_configured

## Whitespace-related #####################################################

# Agda can fail to compile on Windows if files which are CPP-processed
# don't end with a newline character (because we use -Werror).

.PHONY : fix-whitespace
fix-whitespace :
	fix-agda-whitespace

.PHONY : check-whitespace
check-whitespace :
	fix-agda-whitespace --check

.PHONY : install-fix-agda-whitespace
install-fix-agda-whitespace :
	cd src/fix-agda-whitespace && \
	$(CABAL_CMD) install $(CABAL_OPTS)
