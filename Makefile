# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli

SHELL=bash

# Profiling verbosity for library-test
PROFVERB=7

# Various paths and commands

TOP=.

# mk/path.mk uses TOP, so include after the definition of TOP.
include ./mk/paths.mk

include ./mk/cabal.mk

# mk/prtty.mk pretty prints information, depending on whether it is run on Travis on not
include ./mk/pretty.mk
STACK_CMD=stack

# Run in interactive and parallel mode by default

# You can use the $(PARALLEL_TESTS_FILE) file for setting the number of
# parallel tests, e.g.
#   PARALLEL_TESTS = 123

PARALLEL_TESTS_FILE = mk/parallel-tests.mk

ifeq ($(wildcard $(PARALLEL_TESTS_FILE)),)
# Setting the default value.
PARALLEL_TESTS = $(shell getconf _NPROCESSORS_ONLN)
else
# Getting the value from the $(PARALLEL_TESTS_FILE) file.
include $(PARALLEL_TESTS_FILE)
endif

AGDA_TESTS_OPTIONS ?=-i -j$(PARALLEL_TESTS)

## Default target #########################################################

.PHONY : default
default: install-bin

## Cabal-based installation ###############################################

.PHONY : install
install: install-bin compile-emacs-mode setup-emacs-mode

.PHONY : prof
prof : install-prof-bin

CABAL_INSTALL_HELPER = $(CABAL_CMD) $(CABAL_INSTALL_CMD) --disable-documentation
STACK_BUILD = $(STACK_CMD) build Agda --no-haddock

# 2016-07-15. We use a different build directory in the quick
# installation for avoiding recompilation (see Issue #2083 and
# https://github.com/haskell/cabal/issues/1893).

QUICK_BUILD_DIR     = $(BUILD_DIR)-quick
QUICK_CABAL_INSTALL = $(CABAL_INSTALL_HELPER) --builddir=$(QUICK_BUILD_DIR)

QUICK_STACK_BUILD_WORK_DIR = .stack-work-quick
QUICK_STACK_BUILD = $(STACK_BUILD) \
                    --ghc-options=-O0 \
                    --work-dir=$(QUICK_STACK_BUILD_WORK_DIR)

SLOW_CABAL_INSTALL_OPTS = --builddir=$(BUILD_DIR) --enable-tests
CABAL_INSTALL           = $(CABAL_INSTALL_HELPER) \
                          $(SLOW_CABAL_INSTALL_OPTS)

# The following options are used in several invocations of cabal
# install/configure below. They are always the last options given to
# the command.
CABAL_INSTALL_OPTS = -fenable-cluster-counting --ghc-options="+RTS -M3G -RTS" $(CABAL_OPTS)

CABAL_INSTALL_BIN_OPTS = --disable-library-profiling \
                         $(CABAL_INSTALL_OPTS)

CABAL_CONFIGURE_OPTS = $(SLOW_CABAL_INSTALL_OPTS) \
                       $(CABAL_INSTALL_BIN_OPTS)

STACK_INSTALL_OPTS     = --flag Agda:enable-cluster-counting $(STACK_OPTS)
STACK_INSTALL_BIN_OPTS = --test \
                         --no-run-tests \
                         --no-library-profiling \
                         $(STACK_INSTALL_OPTS)

# Ensures that the Git hash that is sometimes displayed by --version
# is correct (#2988).
.PHONY : ensure-hash-is-correct
ensure-hash-is-correct :
	touch src/full/Agda/VersionCommit.hs

.PHONY : quick-install-bin
quick-install-bin : ensure-hash-is-correct
	$(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)

.PHONY : quicker-stack-install-bin
quicker-stack-install-bin: ensure-hash-is-correct
	$(QUICK_STACK_BUILD) $(STACK_INSTALL_BIN_OPTS)

.PHONY : quicker-stack-copy-artefacts
quicker-stack-copy-artefacts : quicker-stack-install-bin
	mkdir -p $(QUICK_BUILD_DIR)/build/
	cp -r $(shell stack path --dist-dir --work-dir=$(QUICK_STACK_BUILD_WORK_DIR))/build $(QUICK_BUILD_DIR)

# Disabling optimizations leads to *much* quicker build times.
# The performance loss is acceptable for running small tests.
.PHONY : quicker-install-bin
quicker-install-bin : ensure-hash-is-correct
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	time $(MAKE) quicker-stack-copy-artefacts
else
	time $(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS) --ghc-options=-O0 --program-suffix=-quicker
endif

# The Stack version of `Cabal install --enable-test`
.PHONY : stack-install-bin
stack-install-bin:
	$(STACK_BUILD) $(STACK_INSTALL_BIN_OPTS)

# Copy the artefacts built by Stack as if they were build by Cabal.
.PHONY : stack-copy-artefacts
stack-copy-artefacts : stack-install-bin
	mkdir -p $(BUILD_DIR)/build/
	cp -r $(shell stack path --dist-dir)/build $(BUILD_DIR)

.PHONY : install-bin
install-bin : ensure-hash-is-correct
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	@echo "===================== Installing using Stack ============================="
	time $(MAKE) stack-copy-artefacts
else
	@echo "===================== Installing using Cabal ============================="
	time $(CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)
endif

.PHONY : install-prof-bin
install-prof-bin : ensure-hash-is-correct
	$(CABAL_INSTALL) --enable-library-profiling --enable-profiling \
          --program-suffix=_p $(CABAL_INSTALL_OPTS)

# --program-suffix is not for the executable name in
# $(BUILD_DIR)/build/, only for installing it into .cabal/bin

# Builds Agda with the debug flag enabled. A separate build directory
# is used. The suffix "-debug" is used for the binaries.

.PHONY : install-debug
install-debug : ensure-hash-is-correct
	$(CABAL_INSTALL) --disable-library-profiling \
        -fdebug --program-suffix=-debug --builddir=$(BUILD_DIR)-debug \
        $(CABAL_INSTALL_OPTS)

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

## Making and testing the Haddock documentation ##############################

.PHONY : haddock
haddock :
	$(CABAL_CMD) configure $(CABAL_CONFIGURE_OPTS)
	$(CABAL_CMD) haddock --builddir=$(BUILD_DIR)

## Making the user manual ####################################################

.PHONY : user-manual-html
user-manual-html :
	@$(call decorate, "User Manual (html)", $(MAKE) -C doc/user-manual html)

.PHONY : user-manual-pdf
user-manual-pdf :
	@$(call decorate, "User Manual (pdf)", $(MAKE) -C doc/user-manual latexpdf)
	cp doc/user-manual/_build/latex/Agda.pdf doc/user-manual.pdf

.PHONY : user-manual-linkcheck
user-manual-linkcheck :
	@$(call decorate, "User Manual (linkcheck)", $(MAKE) -C doc/user-manual linkcheck)
	cp doc/user-manual/_build/latex/Agda.pdf doc/user-manual.pdf

## Making the full language ###############################################

$(AGDA_BIN): ensure-hash-is-correct
	$(CABAL_CMD) build $(CABAL_OPTS)

.PHONY : full
full : $(AGDA_BIN)

## Making the source distribution #########################################

.PHONY : tags
tags :
	$(MAKE) -C $(FULL_SRC_DIR) tags

.PHONY : TAGS
TAGS :
	@$(call decorate,"TAGS", \
		$(MAKE) -C $(FULL_SRC_DIR) TAGS)

## Testing ################################################################

.PHONY : quick
quick : install-O0-bin quicktest

.PHONY : test
test : check-whitespace succeed fail bugs interaction examples library-test interactive latex-html-test api-test internal-tests benchmark-without-logs compiler-test stdlib-compiler-test lib-succeed lib-interaction user-manual-test test-size-solver

.PHONY : quicktest
quicktest : succeed fail

.PHONY : internal-tests
internal-tests :
	@$(call decorate, "Internal test suite", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Internal )

.PHONY : succeed
succeed :
	@$(call decorate, "Suite of Successful tests", \
		$(MAKE) -C test/Common; \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Succeed )

.PHONY : interaction
interaction :
	@$(call decorate, "Suite of interaction tests", \
		$(MAKE) -C test/interaction)

.PHONY : interactive
interactive :
	@$(call decorate, "Suite of interactive tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Interactive)

.PHONY : examples
examples :
	@$(call decorate, "Suite of examples", \
		$(MAKE) -C examples)

.PHONY : fail
fail :
	@$(call decorate, "Suite of failing tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Fail)

.PHONY : bugs
bugs :
	@$(call decorate, "Suite of tests for bugs", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Bugs)

.PHONY : latex-html-test
latex-html-test :
	@$(call decorate, "Suite of tests for the LaTeX and HTML backends", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXAndHTML)

.PHONY : html-test
html-test :
	@$(call decorate, "Suite of tests for the HTML backend", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/HTMLOnly)

.PHONY : latex-test
latex-test :
	@$(call decorate, "Suite of tests for the LaTeX backend", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXOnly)

.PHONY : quicklatex-test
quicklatex-test :
	@$(call decorate, "Suite of tests for the QuickLaTeX backend", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/QuickLaTeXOnly)

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
	@$(call decorate, "Standard library", \
		(cd std-lib && runhaskell GenerateEverything.hs && \
						time $(AGDA_BIN) $(AGDA_OPTS) --ignore-interfaces --no-default-libraries -v profile:$(PROFVERB) \
														 -i. -isrc README.agda \
														 +RTS -s))

.PHONY : continue-library-test
continue-library-test :
	@(cd std-lib && \
          time $(AGDA_BIN) -v profile:$(PROFVERB) --no-default-libraries -i. -isrc README.agda +RTS -s)

.PHONY : lib-succeed
lib-succeed :
	@$(call decorate, "Successful tests using the standard library", \
	  find test/LibSucceed -type f -name '*.agdai' -delete ; \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LibSucceed)

.PHONY : lib-interaction
lib-interaction :
	@$(call decorate, "Interaction tests using the standard library", \
	  $(MAKE) -C test/$@)

.PHONY : compiler-test
compiler-test :
	@$(call decorate, "Compiler tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Compiler --regex-exclude AllStdLib)

.PHONY : stdlib-compiler-test
stdlib-compiler-test :
	@$(call decorate, "Standard Library Compiler tests", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include AllStdLib)

.PHONY : api-test
api-test :
	@$(call decorate, "Successful tests using Agda as a Haskell library", \
		$(MAKE) -C test/api clean; $(MAKE) -C test/api)

.PHONY : benchmark
benchmark :
	@$(call decorate, "Benchmark suite", \
		$(MAKE) -C benchmark)

.PHONY : benchmark-without-logs
benchmark-without-logs :
	@$(call decorate, "Benchmark suite without creating logs", \
	  $(MAKE) -C benchmark without-creating-logs)

.PHONY : user-manual-test
user-manual-test :
	@$(call decorate, "User manual", \
		find doc/user-manual -type f -name '*.agdai' -delete; \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/UserManual)

.PHONY : testing-emacs-mode
testing-emacs-mode:
	@$(call decorate, "Testing the Emacs mode", \
	  $(AGDA_MODE) compile)

## Clean ##################################################################

clean_helper = if [ -d $(1) ]; then $(CABAL_CMD) $(CABAL_CLEAN_CMD) --builddir=$(1); fi;


.PHONY : clean
clean :
	$(call clean_helper,$(BUILD_DIR))
	$(call clean_helper,$(QUICK_BUILD_DIR))

## Whitespace-related #####################################################

# Agda can fail to compile on Windows if files which are CPP-processed
# don't end with a newline character (because we use -Werror).

FAW_PATH = src/fix-agda-whitespace
FAW_BIN  = $(FAW_PATH)/dist/build/fix-agda-whitespace/fix-agda-whitespace

.PHONY : fix-whitespace
fix-whitespace : build-fix-agda-whitespace
	$(FAW_BIN)

.PHONY : check-whitespace
check-whitespace : build-fix-agda-whitespace
	$(FAW_BIN) --check

.PHONY : build-fix-agda-whitespace
build-fix-agda-whitespace :
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	stack build fix-agda-whitespace
	mkdir -p $(FAW_PATH)/dist/build/fix-agda-whitespace/
	cp $(shell stack path --local-install-root)/bin/fix-agda-whitespace $(FAW_BIN)
else
	cd $(FAW_PATH) && $(CABAL_CMD) $(CABAL_CLEAN_CMD) && $(CABAL_CMD) $(CABAL_BUILD_CMD)
endif

## size-solver standalone program #########################################

# NB. It is necessary to install the Agda library (i.e run `make install-bin`)
# before installing the `size-solver` program.
.PHONY : install-size-solver
install-size-solver :
	@$(call decorate, "Installing the size-solver program", \
		$(MAKE) -C src/size-solver install-bin)

.PHONY : test-size-solver
test-size-solver : install-size-solver
	@$(call decorate, "Testing the size-solver program", \
		$(MAKE) -C src/size-solver test)

## agda-bisect standalone program #########################################

.PHONY : install-agda-bisect
install-agda-bisect :
	@$(call decorate, "Installing the agda-bisect program", \
		cd src/agda-bisect && $(CABAL_CMD) $(CABAL_INSTALL_CMD))

###########################################################################
# HPC

.PHONY: hpc-build
hpc-build: ensure-hash-is-correct
	$(CABAL_CMD) clean $(CABAL_OPTS)
	$(CABAL_CMD) configure --enable-library-coverage $(CABAL_INSTALL_OPTS)
	$(CABAL_CMD) build $(CABAL_OPTS)

agda.tix: ./examples/agda.tix ./test/Succeed/agda.tix ./test/compiler/agda.tix ./test/api/agda.tix ./test/interaction/agda.tix ./test/fail/agda.tix ./test/lib-succeed/agda.tix ./std-lib/agda.tix
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

###########################################################################
# Module dependency graph

mod-dep : module-dependency-graph.pdf
mod-dot : module-dependency-graph.dot

module-dependency-graph.pdf : %.pdf : %.dot
	dot -Tpdf $< > $@

module-dependency-graph.dot : Agda.cabal Makefile
	graphmod --no-cluster --prune-edges > $@


###########################################################################
# HLint

hlint : $(BUILD_DIR)/build/autogen/cabal_macros.h
	hlint --cpp-file=$< \
              --cpp-include=$(FULL_SRC_DIR) \
	      --report=hlint-report.html \
	      $(FULL_SRC_DIR)/Agda

###########################################################################
# Debug

debug :
	@echo "AGDA_BIN           = $(AGDA_BIN)"
	@echo "AGDA_TESTS_BIN     = $(AGDA_TESTS_BIN)"
	@echo "AGDA_TESTS_OPTIONS = $(AGDA_TESTS_OPTIONS)"
	@echo "BUILD_DIR          = $(BUILD_DIR)"
	@echo "CABAL_CMD          = $(CABAL_CMD)"
	@echo "CABAL_OPTS         = $(CABAL_OPTS)"
	@echo "GHC_VERSION        = $(GHC_VERSION)"
	@echo "PARALLEL_TESTS     = $(PARALLEL_TESTS)"

# EOF
