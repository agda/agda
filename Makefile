# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli

SHELL=bash

# Profiling verbosity for library-test
PROFVERB=7

# Various paths and commands

TOP=.
# mk/path.mk uses TOP, so include after the definition of TOP.
include ./mk/paths.mk

CABAL_CMD=cabal

# check if this is GHC 7.10 or newer
GHC_GTEQ_710 := $(shell expr `ghc --numeric-version | sed -e 's/\.\([0-9][0-9]\)/\1/g' -e 's/\.\([0-9]\)/0\1/g' -e 's/^[0-9]\{3,4\}$$/&00/'` \>= 71000)

ifneq ($(shell which uhc),)
ifeq "$(GHC_GTEQ_710)" "1"
override CABAL_OPTS+=-fuhc
endif
endif

override CABAL_OPTS+=--builddir=$(BUILD_DIR)

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
	$(CABAL_CMD) install --enable-tests --disable-documentation \
	  --disable-library-profiling $(CABAL_OPTS)

.PHONY : install-O0-bin
install-O0-bin :
	$(CABAL_CMD) install -O0 --enable-tests --disable-documentation \
	  --disable-library-profiling $(CABAL_OPTS)

.PHONY : install-O2-bin
install-O2-bin :
	$(CABAL_CMD) install -O2 --enable-tests --disable-documentation \
	  --disable-library-profiling $(CABAL_OPTS)

.PHONY : install-prof-bin
install-prof-bin :
	$(CABAL_CMD) install --enable-tests --disable-documentation \
	  --enable-library-profiling --enable-profiling \
          --program-suffix=_p $(CABAL_OPTS)

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
	$(CABAL_CMD) configure --builddir=$(BUILD_DIR) --enable-tests
	$(CABAL_CMD) haddock --builddir=$(BUILD_DIR) --tests

.PHONY : manual-html
manual-html:
	$(MAKE) -C doc/user-manual html

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
	@echo "======================================================================"
	@echo "================================ TAGS ================================"
	@echo "======================================================================"
	$(MAKE) -C $(FULL_SRC_DIR) TAGS

## Testing ###########################################################

.PHONY : quick
quick : install-O0-bin quicktest

.PHONY : test
# We don't run the `epic-test` because the Epic backend has been
# disabled. See Issue 1481.
test : check-whitespace succeed fail interaction interactive latex-html-test examples library-test api-test tests benchmark-without-logs compiler-test lib-succeed lib-interaction

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
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Succeed

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
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Fail
	@$(MAKE) -C test/Fail

.PHONY : latex-html-test
latex-html-test :
	@echo "======================================================================"
	@echo "=========== Suite of tests for the LaTeX and HTML backends ==========="
	@echo "======================================================================"
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXAndHTML

.PHONY : std-lib
std-lib :
	git submodule update --init std-lib

.PHONY : up-to-date-std-lib
up-to-date-std-lib :
	git submodule update --init std-lib
	@(cd std-lib && make setup)

.PHONY : fast-forward-std-lib
fast-forward-std-lib :
	git submodule update --init --remote std-lib
	@(cd std-lib && make setup)

.PHONY : library-test
library-test : # up-to-date-std-lib
	@echo "======================================================================"
	@echo "========================== Standard library =========================="
	@echo "======================================================================"
	(cd std-lib && runhaskell GenerateEverything.hs && \
          time $(AGDA_BIN) --ignore-interfaces --no-default-libraries -v profile:$(PROFVERB) \
                           -i. -isrc README.agda \
                           +RTS -s -H1G -M1.5G)

.PHONY : continue-library-test
continue-library-test :
	@(cd std-lib && \
          time $(AGDA_BIN) -v profile:$(PROFVERB) --no-default-libraries -i. -isrc README.agda +RTS -s -H1G -M1.5G)

.PHONY : lib-succeed
lib-succeed :
	@echo "======================================================================"
	@echo "========== Successfull tests using the standard library =============="
	@echo "======================================================================"
	@find test/LibSucceed -type f -name '*.agdai' -delete
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LibSucceed

.PHONY : lib-interaction
lib-interaction :
	@echo "======================================================================"
	@echo "========== Interaction tests using the standard library =============="
	@echo "======================================================================"
	@$(MAKE) -C test/$@

# The Epic backend has been removed. See Issue 1481.
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
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Compiler

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

agda.tix: ./examples/agda.tix ./test/Succeed/agda.tix ./test/compiler/agda.tix ./test/api/agda.tix ./test/interaction/agda.tix ./test/fail/agda.tix ./test/fail/Epic/agda.tix ./test/lib-succeed/agda.tix ./std-lib/agda.tix
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

##############################################################################
# HLint

hlint : $(BUILD_DIR)/build/autogen/cabal_macros.h
	hlint --cpp-file=$< \
              --cpp-include=$(FULL_SRC_DIR) \
	      --report=hlint-report.html \
	      $(FULL_SRC_DIR)/Agda

# EOF
