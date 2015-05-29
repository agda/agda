# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli

SHELL=bash

# Profiling verbosity for library-test
PROFVERB=7

# Agda standard library branch.
STD_LIB_BRANCH = 2.4.2.4

# The GHC version.
GHC_VERSION=$(shell ghc --numeric-version)

# Stack size for library-test [Issue 1521].
ifeq ($(GHC_VERSION), 7.4.2)
STACK_SIZE=-K16M
endif

# Various paths and commands

TOP=.
# mk/path.mk uses TOP, so include after the definition of TOP.
include ./mk/paths.mk

CABAL_CMD=cabal

override CABAL_OPTS+=--builddir=$(BUILD_DIR)

ifndef RELEASE

  # --program-suffix is not for the executable name in
  # $(BUILD_DIR)/build/, only for installing it into .cabal/bin
  override CABAL_OPTS+=--program-suffix=-$(VERSION)

  AGDA_MODE=agda-mode-$(VERSION)

else

  AGDA_MODE=agda-mode

endif

# Run in interactive and parallel mode by default
AGDA_TESTS_OPTIONS ?=-i -j $(shell getconf _NPROCESSORS_ONLN)

## Default target #########################################################

.PHONY : default
default: install-bin

## Cabal-based installation ###############################################

.PHONY : install
install: install-bin compile-emacs-mode setup-emacs-mode

.PHONY : prof
prof : install-prof-bin

.PHONY : install-bin
install-bin :
	$(CABAL_CMD) install --enable-tests --disable-library-profiling --disable-documentation $(CABAL_OPTS)

.PHONY : install-O0-bin
install-O0-bin :
	$(CABAL_CMD) install -O0 --disable-library-profiling --disable-documentation $(CABAL_OPTS)

.PHONY : install-O2-bin
install-O2-bin :
	$(CABAL_CMD) install -O2 --disable-library-profiling --disable-documentation $(CABAL_OPTS)

.PHONY : install-prof-bin
install-prof-bin :
	$(CABAL_CMD) install --enable-library-profiling --enable-profiling \
                             --program-suffix=_p --disable-documentation $(CABAL_OPTS)

.PHONY : compile-emacs-mode
compile-emacs-mode: install-bin
	$(AGDA_MODE) compile

.PHONY : setup-emacs-mode
setup-emacs-mode : install-bin
	@echo
	@echo "If the agda-mode command is not found, make sure that the directory"
	@echo "in which it was installed is located on your shell's search path."
	@echo
	$(AGDA_MODE) setup

## Making the documentation ###############################################

.PHONY : doc
doc:
	$(CABAL_CMD) configure $(CABAL_OPTS)
	$(CABAL_CMD) haddock $(CABAL_OPTS)

## Making the full language ###############################################

$(AGDA_BIN):
	$(CABAL_CMD) build $(CABAL_OPTS)

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
# We don't run the `epic-test` because the Epic backend has been
# disabled. See Issue 1481.
test : check-whitespace succeed fail interaction interactive latex-test examples library-test api-test tests benchmark-without-logs compiler-test lib-succeed

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
	@$(MAKE) -C test/Common
	@chmod +x test/succeed/checkOutput
	@$(MAKE) -C test/succeed

.PHONY : interaction
interaction :
	@echo "======================================================================"
	@echo "===================== Suite of interaction tests ====================="
	@echo "======================================================================"
	@$(MAKE) -C test/interaction

.PHONY : interactive
interactive :
	@echo "======================================================================"
	@echo "===================== Suite of interactive tests ====================="
	@echo "======================================================================"
	@$(MAKE) -C test/interactive

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
	   git clone https://github.com/agda/agda-stdlib.git \
	       --branch $(STD_LIB_BRANCH) --single-branch $@; \
	fi

.PHONY : up-to-date-std-lib
up-to-date-std-lib : std-lib
	@(cd std-lib && \
	  git fetch && \
          git checkout $(STD_LIB_BRANCH) && \
          git merge origin/$(STD_LIB_BRANCH) && \
	  make setup)

.PHONY : library-test
library-test : # up-to-date-std-lib
	@echo "======================================================================"
	@echo "========================== Standard library =========================="
	@echo "======================================================================"
	(cd std-lib && runhaskell GenerateEverything.hs && \
          time $(AGDA_BIN) --ignore-interfaces -v profile:$(PROFVERB) \
                           -i. -isrc README.agda \
                           +RTS -s -H1G -M1.5G $(STACK_SIZE))

.PHONY : continue-library-test
continue-library-test :
	@(cd std-lib && \
          time $(AGDA_BIN) -v profile:$(PROFVERB) -i. -isrc README.agda +RTS -s -H1G -M1.5G)

.PHONY : lib-succeed
lib-succeed :
	@echo "======================================================================"
	@echo "========== Successfull tests using the standard library =============="
	@echo "======================================================================"
	@$(MAKE) -C test/$@

# The Epic backend has been disabled. See Issue 1481.
.PHONY : epic-test
epic-test :
	@echo "======================================================================"
	@echo "============================ Epic backend ============================"
	@echo "======================================================================"
	@$(MAKE) -C test/epic

.PHONY : compiler-test
compiler-test :
	@echo "======================================================================"
	@echo "========================== Compiler tests ============================"
	@echo "======================================================================"
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS)

.PHONY : api-test
api-test :
	@echo "======================================================================"
	@echo "======== Successfull tests using Agda as a Haskell library ==========="
	@echo "======================================================================"
	@$(MAKE) -C test/api

.PHONY : benchmark
benchmark :
	@echo "======================================================================"
	@echo "========================= Benchmark suite ============================"
	@echo "======================================================================"
	@$(MAKE) -C benchmark

.PHONY : benchmark-without-logs
benchmark-without-logs :
	@echo "======================================================================"
	@echo "============ Benchmark suite without creating logs ==================="
	@echo "======================================================================"
	@$(MAKE) -C benchmark without-creating-logs

## Clean ##################################################################

.PHONY : clean
clean :
	$(CABAL_CMD) clean --builddir=$(BUILD_DIR)

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
	cd src/fix-agda-whitespace && $(CABAL_CMD) install

########################################################################
# HPC

.PHONY: hpc-build
hpc-build:
	$(CABAL_CMD) clean $(CABAL_OPTS)
	$(CABAL_CMD) configure --enable-library-coverage $(CABAL_OPTS)
	$(CABAL_CMD) build $(CABAL_OPTS)

agda.tix: ./examples/agda.tix ./test/succeed/agda.tix ./test/compiler/agda.tix ./test/api/agda.tix ./test/interaction/agda.tix ./test/fail/agda.tix ./test/fail/Epic/agda.tix ./test/lib-succeed/agda.tix ./std-lib/agda.tix
	hpc sum --output=$@ $^

.PHONY: hpc
hpc: hpc-build test agda.tix
	hpc report --hpcdir=$(BUILD_DIR)/hpc/mix/Agda-$(VERSION) agda.tix
	hpc markup --hpcdir=$(BUILD_DIR)/hpc/mix/Agda-$(VERSION) agda --destdir=hpc-report

## Lines of Code ##########################################################

agdalocfiles=$(shell find . \( \( -name '*.agda' -o -name '*.in' \) ! -name '.*' \) )

# Agda files (tests) in this project

agda-loc :
	@wc $(agdalocfiles)

# Source code of Agda

loc :
	make -C src/full loc

# EOF
