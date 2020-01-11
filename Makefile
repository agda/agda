# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli, Liang-Ting Chen

SHELL=bash

# Profiling verbosity for std-lib-test
PROFVERB=7

# Various paths and commands

TOP=.

# mk/path.mk uses TOP, so include after the definition of TOP.
include ./mk/paths.mk
include ./mk/cabal.mk
STACK_CMD=stack

# mk/prtty.mk pretty prints information, depending on whether it is run on Travis on not
include ./mk/pretty.mk

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

CABAL_INSTALL_HELPER = $(CABAL_CMD) $(CABAL_INSTALL_CMD) --disable-documentation
STACK_INSTALL_HELPER = $(STACK_CMD) install Agda --no-haddock --system-ghc

# 2016-07-15. We use a different build directory in the quick
# installation for avoiding recompilation (see Issue #2083 and
# https://github.com/haskell/cabal/issues/1893).

QUICK_BUILD_DIR       = $(BUILD_DIR)-quick
QUICK_STACK_BUILD_DIR = .stack-work-quick

QUICK_CABAL_INSTALL = $(CABAL_INSTALL_HELPER) --builddir=$(QUICK_BUILD_DIR)
QUICK_STACK_INSTALL = $(STACK_INSTALL_HELPER) --work-dir=$(QUICK_STACK_BUILD_DIR)

SLOW_CABAL_INSTALL_OPTS = --builddir=$(BUILD_DIR) --enable-tests
SLOW_STACK_INSTALL_OPTS = --test --no-run-tests

CABAL_INSTALL           = $(CABAL_INSTALL_HELPER) \
                          $(SLOW_CABAL_INSTALL_OPTS)
STACK_INSTALL           = $(STACK_INSTALL_HELPER) \
                          $(SLOW_STACK_INSTALL_OPTS)

# The following options are used in several invocations of cabal
# install/configure below. They are always the last options given to
# the command.
GHC_OPTS           = "+RTS -M3G -RTS"
CABAL_INSTALL_OPTS = -fenable-cluster-counting --ghc-options=$(GHC_OPTS) $(CABAL_OPTS)
STACK_INSTALL_OPTS = --flag Agda:enable-cluster-counting --ghc-options $(GHC_OPTS) $(STACK_OPTS)

CABAL_INSTALL_BIN_OPTS = --disable-library-profiling \
                         $(CABAL_INSTALL_OPTS)
STACK_INSTALL_BIN_OPTS = --no-library-profiling \
                         $(STACK_INSTALL_OPTS)

CABAL_CONFIGURE_OPTS = $(SLOW_CABAL_INSTALL_OPTS) \
                       $(CABAL_INSTALL_BIN_OPTS)

##############################################################################
## Installation

.PHONY: default
default: install-bin

.PHONY: install ## Install Agda, test suites, and Emacs mode via cabal (or stack if stack.yaml is exists).
install: install-bin compile-emacs-mode setup-emacs-mode

.PHONY: ensure-hash-is-correct
ensure-hash-is-correct:
	touch src/full/Agda/VersionCommit.hs

.PHONY: install-bin ## Install Agda and test suites via cabal (or stack if stack.yaml exists).
install-bin: ensure-hash-is-correct
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	@echo "===================== Installing using Stack with test suites ============"
	time $(STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
	mkdir -p $(BUILD_DIR)/build/
	cp -r $(shell stack path --dist-dir)/build $(BUILD_DIR)
else
	@echo "===================== Installing using Cabal with test suites ============"
# `cabal new-install --enable-tests` emits the error message (bug?):
# cabal: --enable-tests was specified, but tests can't be enabled in a remote package
	@echo "===================== Installing using Cabal with test suites ============"
	time $(CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)
endif

.PHONY: quick-install-bin ## Install Agda via cabal (or stack if stack.yaml exists).
quick-install-bin: ensure-hash-is-correct
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	@echo "===================== Installing using Stack ============================="
	$(QUICK_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
else
	@echo "===================== Installing using Cabal ============================="
	$(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)
endif

# Disabling optimizations leads to *much* quicker build times.
# The performance loss is acceptable for running small tests.

.PHONY: quicker-install-bin ## Install Agda (compiled with -O0) via cabal (or stack if stack.yaml exists).
quicker-install-bin: ensure-hash-is-correct
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	@echo "===================== Installing using Stack with -O0 ===================="
	time $(QUICK_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS) --fast
else
	@echo "===================== Installing using Cabal with -O0 ===================="
	time $(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS) --ghc-options=-O0 --program-suffix=-quicker
endif

.PHONY : install-prof-bin ## Install Agda with profiling enabled via cabal.
install-prof-bin : ensure-hash-is-correct
	$(CABAL_INSTALL) --enable-library-profiling --enable-profiling \
          --program-suffix=_p $(CABAL_INSTALL_OPTS)

# --program-suffix is not for the executable name in
# $(BUILD_DIR)/build/, only for installing it into .cabal/bin

# Builds Agda with the debug flag enabled. A separate build directory
# is used. The suffix "-debug" is used for the binaries.

.PHONY : install-debug ## Install Agda with debug enabled via cabal.
install-debug : ensure-hash-is-correct
	$(CABAL_INSTALL) --disable-library-profiling \
        -fdebug --program-suffix=-debug --builddir=$(BUILD_DIR)-debug \
        $(CABAL_INSTALL_OPTS)

.PHONY : compile-emacs-mode ## Compile Agda's Emacs mode using Emacs.
compile-emacs-mode: install-bin
	$(AGDA_MODE) compile

.PHONY : setup-emacs-mode ## Configure Agda's Emacs mode.
setup-emacs-mode : install-bin
	@echo
	@echo "If the agda-mode command is not found, make sure that the directory"
	@echo "in which it was installed is located on your shell's search path."
	@echo
	$(AGDA_MODE) setup

## Clean ####################################################################
clean_helper = if [ -d $(1) ]; then $(CABAL_CMD) $(CABAL_CLEAN_CMD) --builddir=$(1); fi;

clean : ## Clean all local builds
	$(call clean_helper,$(BUILD_DIR))
	$(call clean_helper,$(QUICK_BUILD_DIR))
	stack clean --full
	stack clean --full --work-dir=$(QUICK_STACK_BUILD_DIR)

## Haddock ###################################################################

.PHONY : haddock ##
haddock :
	$(CABAL_CMD) $(CABAL_CONFIGURE_CMD) $(CABAL_CONFIGURE_OPTS)
	$(CABAL_CMD) $(CABAL_HADDOCK_CMD) --builddir=$(BUILD_DIR)

##############################################################################
## The user manual

.PHONY : user-manual-html ## Make the user manual (HTML).
user-manual-html :
	@$(call decorate, "User manual (HTML)", $(MAKE) -C doc/user-manual html)

.PHONY : user-manual-pdf ## Make the user manual (PDF).
user-manual-pdf :
	@$(call decorate, "User manual (PDF)", $(MAKE) -C doc/user-manual latexpdf)
	cp doc/user-manual/_build/latex/Agda.pdf doc/user-manual.pdf

.PHONY: user-manual-linkcheck ##
user-manual-linkcheck :
	@$(call decorate, "User manual (linkcheck)", $(MAKE) -C doc/user-manual linkcheck)
	cp doc/user-manual/_build/latex/Agda.pdf doc/user-manual.pdf

##############################################################################
## Making the source distribution

.PHONY : tags ##
tags :
	$(MAKE) -C $(FULL_SRC_DIR) tags

.PHONY : TAGS ##
TAGS :
	@$(call decorate, "TAGS", \
		$(MAKE) -C $(FULL_SRC_DIR) TAGS)

##############################################################################
## Standard library
.PHONY : std-lib ## Update the standard library.
std-lib :
	git submodule update --init std-lib

.PHONY : up-to-date-std-lib ##
up-to-date-std-lib : std-lib
	@(cd std-lib && make setup)

.PHONY : fast-forward-std-lib ##
fast-forward-std-lib :
	git submodule update --init --remote std-lib
	@(cd std-lib && make setup)

##############################################################################
## Testing

.PHONY : test ## Run all test suites.
test : check-whitespace \
       succeed \
       fail \
       bugs \
       interaction \
       examples \
       std-lib-test \
       interactive \
       latex-html-test \
       api-test \
       internal-tests \
       benchmark-without-logs \
       compiler-test \
       std-lib-compiler-test \
       std-lib-succeed \
       std-lib-interaction \
       user-manual-test \
       test-size-solver

.PHONY : test-using-std-lib ## Run all tests which use the standard library.
test-using-std-lib : std-lib-test \
                     benchmark-without-logs \
                     std-lib-compiler-test \
                     std-lib-succeed \
                     std-lib-interaction

.PHONY : quicktest ## Run successful and failing tests.
quicktest : succeed fail

.PHONY : bugs ##
bugs :
	@$(call decorate, "Suite of tests for bugs", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Bugs)

.PHONY : internal-tests ##
internal-tests :
	@$(call decorate, "Internal test suite", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Internal )

.PHONY : succeed ##
succeed :
	@$(call decorate, "Suite of successful tests", \
		$(MAKE) -C test/Common; \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Succeed )

.PHONY : fail ##
fail :
	@$(call decorate, "Suite of failing tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Fail)

.PHONY : interaction ##
interaction :
	@$(call decorate, "Suite of interaction tests", \
		$(MAKE) -C test/interaction)

.PHONY : interactive ##
interactive :
	@$(call decorate, "Suite of interactive tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Interactive)

.PHONY : examples ##
examples :
	@$(call decorate, "Suite of examples", \
		$(MAKE) -C examples)

.PHONY : latex-html-test ## Tests the LaTeX and HTML backends.
latex-html-test :
	@$(call decorate, "Suite of tests for the LaTeX and HTML backends", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXAndHTML)

.PHONY : html-test ##
html-test :
	@$(call decorate, "Suite of tests for the HTML backend", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/HTMLOnly)

.PHONY : latex-test ##
latex-test :
	@$(call decorate, "Suite of tests for the LaTeX backend", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXOnly)

.PHONY : quicklatex-test ##
quicklatex-test :
	@$(call decorate, "Suite of tests for the QuickLaTeX backend", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/QuickLaTeXOnly)

.PHONY : std-library-test ##
std-lib-test :
	@$(call decorate, "Standard library test", \
		(cd std-lib && runhaskell GenerateEverything.hs && \
						time $(AGDA_BIN) $(AGDA_OPTS) --ignore-interfaces --no-default-libraries -v profile:$(PROFVERB) \
														 -i. -isrc README.agda \
														 +RTS -s))

.PHONY : continue-std-lib-test ##
continue-std-lib-test :
	@(cd std-lib && \
          time $(AGDA_BIN) -v profile:$(PROFVERB) --no-default-libraries -i. -isrc README.agda +RTS -s)

.PHONY : std-lib-succeed ##
std-lib-succeed :
	@$(call decorate, "Successful tests using the standard library", \
	  find test/LibSucceed -type f -name '*.agdai' -delete ; \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LibSucceed)

.PHONY : std-lib-interaction ##
std-lib-interaction :
	@$(call decorate, "Interaction tests using the standard library", \
	  $(MAKE) -C test/lib-interaction)

.PHONY : compiler-test ##
compiler-test :
	@$(call decorate, "Compiler tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Compiler --regex-exclude AllStdLib)

.PHONY : std-lib-compiler-test ##
std-lib-compiler-test :
	@$(call decorate, "Standard library compiler tests", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include AllStdLib)

.PHONY : api-test ##
api-test :
	@$(call decorate, "Successful tests using Agda as a Haskell library", \
		$(MAKE) -C test/api clean; $(MAKE) -C test/api)

.PHONY : benchmark ##
benchmark :
	@$(call decorate, "Benchmark suite", \
		$(MAKE) -C benchmark)

.PHONY : benchmark-without-logs ##
benchmark-without-logs :
	@$(call decorate, "Benchmark suite without creating logs", \
	  $(MAKE) -C benchmark without-creating-logs)

.PHONY : user-manual-test ##
user-manual-test :
	@$(call decorate, "User manual (test)", \
		find doc/user-manual -type f -name '*.agdai' -delete; \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/UserManual)

.PHONY : testing-emacs-mode ##
testing-emacs-mode:
	@$(call decorate, "Testing the Emacs mode", \
	  $(AGDA_MODE) compile)

##############################################################################
## Size solver

# NB. It is necessary to install the Agda library (i.e run `make install-bin`)
# before installing the `size-solver` program.
.PHONY : install-size-solver ## Install the size solver.
install-size-solver :
	@$(call decorate, "Installing the size-solver program", \
		$(MAKE) -C src/size-solver install-bin)

.PHONY : test-size-solver ##
test-size-solver : install-size-solver
	@$(call decorate, "Testing the size-solver program", \
		$(MAKE) -C src/size-solver test)

##############################################################################
## Development

## Whitespace-related #######################################################
# Agda can fail to compile on Windows if files which are CPP-processed
# don't end with a newline character (because we use -Werror).

FAW_PATH = src/fix-agda-whitespace
FAW_BIN  = $(FAW_PATH)/dist/build/fix-agda-whitespace/fix-agda-whitespace

.PHONY : fix-whitespace ## Fix the whitespace issue.
fix-whitespace : build-fix-agda-whitespace
	$(FAW_BIN)

.PHONY : check-whitespace ## Check the whitespace issue without fixing it.
check-whitespace : build-fix-agda-whitespace
	$(FAW_BIN) --check

.PHONY : build-fix-agda-whitespace ## Build fix-agda-whitespace.
build-fix-agda-whitespace :
ifneq ("$(wildcard stack.yaml)","") # if `stack.yaml` exists
	stack build fix-agda-whitespace
	mkdir -p $(FAW_PATH)/dist/build/fix-agda-whitespace/
	cp $(shell stack path --local-install-root)/bin/fix-agda-whitespace $(FAW_BIN)
else
	cd $(FAW_PATH) && $(CABAL_CMD) $(CABAL_CLEAN_CMD) && $(CABAL_CMD) $(CABAL_BUILD_CMD)
endif

## agda-bisect standalone program ############################################
.PHONY : install-agda-bisect ## Install agda-bisect.
install-agda-bisect :
	@$(call decorate, "Installing the agda-bisect program", \
		cd src/agda-bisect && $(CABAL_CMD) $(CABAL_INSTALL_CMD))

## HPC #######################################################################
.PHONY: hpc-build ##
hpc-build: ensure-hash-is-correct
	$(CABAL_CMD) $(CABAL_CLEAN_CMD) $(CABAL_OPTS)
	$(CABAL_CMD) $(CABAL_CONFIGURE_CMD) --enable-library-coverage $(CABAL_INSTALL_OPTS)
	$(CABAL_CMD) $(CABAL_BUILD_CMD) $(CABAL_OPTS)

agda.tix: ./examples/agda.tix ./test/Succeed/agda.tix ./test/compiler/agda.tix ./test/api/agda.tix ./test/interaction/agda.tix ./test/fail/agda.tix ./test/lib-succeed/agda.tix ./std-lib/agda.tix ##
	hpc sum --output=$@ $^

.PHONY: hpc ## Generate a code coverage report via cabal.
hpc: hpc-build test agda.tix
	hpc report --hpcdir=$(BUILD_DIR)/hpc/mix/Agda-$(VERSION) agda.tix
	hpc markup --hpcdir=$(BUILD_DIR)/hpc/mix/Agda-$(VERSION) agda --destdir=hpc-report

## Lines of Code #############################################################

agdalocfiles=$(shell find . \( \( -name '*.agda' -o -name '*.in' \) ! -name '.*' \) )

agda-loc : ## Agda files (tests) in this project
	@wc $(agdalocfiles)

loc : ## Source code of Agda
	make -C src/full loc

## Module dependency graph ###################################################

mod-dep : module-dependency-graph.pdf ## Generate a module dependency graph (PDF).
mod-dot : module-dependency-graph.dot ## Generate a module dependency graph (DOT).

module-dependency-graph.pdf : %.pdf : %.dot
	dot -Tpdf $< > $@

module-dependency-graph.dot :
	graphmod --no-cluster --prune-edges > $@

## HLint ####################################################################

hlint : $(BUILD_DIR)/build/autogen/cabal_macros.h ##
	hlint --cpp-file=$< \
              --cpp-include=$(FULL_SRC_DIR) \
	      --report=hlint-report.html \
	      $(FULL_SRC_DIR)/Agda

##############################################################################
## Auxiliary targets

help: ## Display this information.
	@echo "Available targets:"
	@sed -n \
		-e 's/^\.PHONY[[:blank:]]*:[[:blank:]]*\([[:graph:]]*[[:blank:]]*##\)/\1/p' \
		-e 's/\([[:alnum:]_-]\{1,\}\)[[:blank:]]*:[[:blank:]]*[^#]*##[[:blank:]]*\([^\#]*\)$$/\1 ## \2/p' \
		-e 's/^\(#\{2,\}\)$$//p' \
		-e "s/^\(#\{2,\}[[:blank:]]*\)\([^#]\{1,\}\)$$/\2/p" \
		Makefile | \
		awk 'BEGIN {FS = "##"}; \
			NF == 0 { print }; \
			NF == 1 { print $$1 };\
	  	NF == 2 { printf "  \033[36m%-26s\033[0m %s\n", $$1, $$2};'

debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_TESTS_BIN        = $(AGDA_TESTS_BIN)"
	@echo "AGDA_TESTS_OPTIONS    = $(AGDA_TESTS_OPTIONS)"
	@echo "BUILD_DIR             = $(BUILD_DIR)"
	@echo "CABAL_BUILD_CMD       = $(CABAL_BUILD_CMD)"
	@echo "CABAL_CLEAN_CMD       = $(CABAL_CLEAN_CMD)"
	@echo "CABAL_CMD             = $(CABAL_CMD)"
	@echo "CABAL_CONFIGURE_CMD   = $(CABAL_CONFIGURE_CMD)"
	@echo "CABAL_CONFIGURE_OPTS  = $(CABAL_CONFIGURE_OPTS)"
	@echo "CABAL_HADDOCK_CMD     = $(CABAL_HADDOCK_CMD)"
	@echo "CABAL_INSTALL_CMD     = $(CABAL_INSTALL_CMD)"
	@echo "CABAL_INSTALL_OPTS    = $(CABAL_INSTALL_OPTS)"
	@echo "CABAL_OPTS            = $(CABAL_OPTS)"
	@echo "GHC_VERSION           = $(GHC_VERSION)"
	@echo "PARALLEL_TESTS        = $(PARALLEL_TESTS)"
	@echo "STACK_CMD             = $(STACK_CMD)"
	@echo "STACK_INSTALL_OPTS    = $(STACK_INSTALL_OPTS)"
	@echo
	@echo "Run \`make -pq\` to get a detailed report."
	@echo

# EOF
