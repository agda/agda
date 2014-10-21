# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli

# Profiling verbosity for library-test
PROFVERB=7

# Various paths and commands

include ./mk/paths.mk

CABAL_CMD=cabal
CABAL_OPTS=
TOP=.

## Default target #########################################################

.PHONY : default
default: install-bin

## Cabal-based installation ###############################################

# If you want to make use of parallel compilation with ghc>=7.8,
# enable the flag below, or set the "jobs" field in your
# ".cabal/config".
#
# ifeq ($(HAVE_GHC_7_7),Yes)
# override CABAL_OPTS+=--ghc-option=-j3
# endif

.PHONY : install
install: install-bin compile-emacs-mode setup-emacs-mode

.PHONY : prof
prof : install-prof-bin

.PHONY : install-bin
install-bin :
	$(CABAL_CMD) install --disable-library-profiling --disable-documentation $(CABAL_OPTS)

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
compile-emacs-mode: install-bin
	agda-mode compile

.PHONY : setup-emacs-mode
setup-emacs-mode : install-bin
	@echo
	@echo "If the agda-mode command is not found, make sure that the directory"
	@echo "in which it was installed is located on your shell's search path."
	@echo
	agda-mode setup

## Making the documentation ###############################################

.PHONY : doc
doc:
	cabal configure
	cabal haddock

## Making the full language ###############################################

$(AGDA_BIN):
	cabal build

.PHONY : full
full : $(AGDA_BIN)

## Making the source distribution #########################################

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
test : check-whitespace succeed fail interaction latex-test examples library-test lib-succeed compiler-test epic-test api-test tests

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
	@(cd std-lib && runhaskell GenerateEverything.hs && \
          time ../$(AGDA_BIN) --ignore-interfaces -v profile:$(PROFVERB) -i. -isrc README.agda $(AGDA_TEST_FLAGS) \
            +RTS -s -H1G -M1.5G)

.PHONY : continue-library-test
continue-library-test :
	@(cd std-lib && \
          time ../$(AGDA_BIN) -v profile:$(PROFVERB) -i. -isrc README.agda +RTS -s -H1G -M1.5G)

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

.PHONY : api-test
api-test :
	@echo "======================================================================"
	@echo "======== Successfull tests using Agda as a Haskell library ==========="
	@echo "======================================================================"
	@$(MAKE) -C test/api

.PHONY : benchmark
benchmark :
	@$(MAKE) -C benchmark

## Clean ##################################################################

.PHONY : clean
clean :
	cabal clean

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
