# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli, Liang-Ting Chen

# Profiling verbosity for std-lib-test
PROFVERB=7

# Various paths and commands

TOP=.

# mk/path.mk uses TOP, so include after the definition of TOP.
include ./mk/paths.mk
include ./mk/cabal.mk
include ./mk/stack.mk

# mk/prtty.mk pretty prints information, depending on whether it is run on Travis on not
include ./mk/pretty.mk

# Run in interactive and parallel mode by default

# You can use the PARALLEL_TESTS variable to control the number of parallel
# tests. The default is one per processor. Invoke make like this:
#   make PARALLEL_TESTS=123 test
# Or set it in ./mk/config.mk, which is .gitignored
ifeq ($(PARALLEL_TESTS),)
PARALLEL_TESTS := $(shell getconf _NPROCESSORS_ONLN)
endif

AGDA_TESTS_OPTIONS ?=-i -j$(PARALLEL_TESTS)

CABAL_INSTALL_HELPER = $(CABAL) $(CABAL_INSTALL_CMD) --disable-documentation
STACK_INSTALL_HELPER = $(STACK) install Agda --no-haddock

# If running on Travis, use --system-ghc.
# Developers running `make` will usually want to use the GHC version they've
# specified in their stack.yaml. Otherwise they can put that option in
# themselves.
# Note that GitHub workflows currently do not use the Makefile, but instead
# invoke `stack` directly. (See: .github/workflows/stack.yml)
ifneq ($(TRAVIS),)
STACK_INSTALL_HELPER += --system-ghc
endif

# 2016-07-15. We use a different build directory in the quick
# installation for avoiding recompilation (see Issue #2083 and
# https://github.com/haskell/cabal/issues/1893).

# quicker install: -O0, no tests

QUICK_BUILD_DIR       = $(BUILD_DIR)-quick
QUICK_STACK_BUILD_DIR = .stack-work-quick

QUICK_CABAL_INSTALL = $(CABAL_INSTALL_HELPER) --builddir=$(QUICK_BUILD_DIR)
QUICK_STACK_INSTALL = $(STACK_INSTALL_HELPER) --work-dir=$(QUICK_STACK_BUILD_DIR)

# fast install: -O0, but tests

FAST_BUILD_DIR       = $(BUILD_DIR)-fast
FAST_STACK_BUILD_DIR = .stack-work-fast

FAST_CABAL_INSTALL = $(CABAL_INSTALL_HELPER) --builddir=$(FAST_BUILD_DIR) \
                     --enable-tests --ghc-options=-O0 --program-suffix=-fast
FAST_STACK_INSTALL = $(STACK_INSTALL_HELPER) --work-dir=$(FAST_STACK_BUILD_DIR) \
                     --test --no-run-tests --fast

# ordinary install: optimizations and tests

SLOW_CABAL_INSTALL_OPTS = --builddir=$(BUILD_DIR) --enable-tests
SLOW_STACK_INSTALL_OPTS = --test --no-run-tests

CABAL_INSTALL           = $(CABAL_INSTALL_HELPER) \
                          $(SLOW_CABAL_INSTALL_OPTS)
STACK_INSTALL           = $(STACK_INSTALL_HELPER) \
                          $(SLOW_STACK_INSTALL_OPTS)

# Depending on your machine and ghc version you might want to tweak the amount of memory
# given to ghc to compile Agda. To do this set GHC_RTS_OPTS in mk/config.mk (gitignored).
ifeq ($(GHC_RTS_OPTS),)
ifeq ("$(shell $(GHC) --info | grep 'target word size' | cut -d\" -f4)","4")
GHC_RTS_OPTS := -M2.3G
else
ifeq ($(GHC_VERSION),8.10)
GHC_RTS_OPTS := -M6G
else
GHC_RTS_OPTS := -M4G
endif
endif
endif
GHC_OPTS = "+RTS $(GHC_RTS_OPTS) -RTS"

# The following options are used in several invocations of cabal
# install/configure below. They are always the last options given to
# the command.
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

.PHONY: install ## Install Agda, test suites, and Emacs mode via cabal (or stack if stack.yaml exists).
install: install-bin compile-emacs-mode setup-emacs-mode

.PHONY: ensure-hash-is-correct
ensure-hash-is-correct:
	touch src/full/Agda/VersionCommit.hs

.PHONY: install-bin ## Install Agda and test suites via cabal (or stack if stack.yaml exists).
install-bin: ensure-hash-is-correct
ifdef HAS_STACK
	@echo "===================== Installing using Stack with test suites ============"
	time $(STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
	mkdir -p $(BUILD_DIR)/build/
	cp -r $(shell $(STACK) path --dist-dir)/build $(BUILD_DIR)
else
# `cabal new-install --enable-tests` emits the error message (bug?):
# cabal: --enable-tests was specified, but tests can't be enabled in a remote package
	@echo "===================== Installing using Cabal with test suites ============"
	time $(CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)
endif

.PHONY: fast-install-bin ## Install Agda -O0 and test suites via cabal (or stack if stack.yaml exists).
fast-install-bin:
ifdef HAS_STACK
	@echo "============= Installing using Stack with -O0 and test suites ============"
	time $(FAST_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
	mkdir -p $(BUILD_DIR)/build/
	cp -r $(shell $(STACK) path --dist-dir)/build $(BUILD_DIR)
else
# `cabal new-install --enable-tests` emits the error message (bug?):
# cabal: --enable-tests was specified, but tests can't be enabled in a remote package
	@echo "============= Installing using Cabal with -O0 and test suites ============"
	time $(FAST_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)
endif

# Andreas, 2020-06-02, AIM XXXII, quick-install-bin seems obsolete since we have quicker-install-bin
# .PHONY: quick-install-bin ## Install Agda via cabal (or stack if stack.yaml exists).
# quick-install-bin: ensure-hash-is-correct
# ifdef HAS_STACK
# 	@echo "===================== Installing using Stack ============================="
# 	$(QUICK_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
# else
# 	@echo "===================== Installing using Cabal ============================="
# 	$(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS)
# endif

# Disabling optimizations leads to *much* quicker build times.
# The performance loss is acceptable for running small tests.

.PHONY: quicker-install-bin ## Install Agda (compiled with -O0) via cabal (or stack if stack.yaml exists).
quicker-install-bin:
ifdef HAS_STACK
	@echo "===================== Installing using Stack with -O0 ===================="
	time $(QUICK_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS) --fast
else
	@echo "===================== Installing using Cabal with -O0 ===================="
	time $(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS) --ghc-options=-O0 --program-suffix=-quicker
endif

# Type check the Agda source only (-fno-code).
# Takes max 40s; can be quicker than make quicker-install-bin (max 5min).
#
# Might "fail" with errors like
#
#   ar: ./dist-2.6.2-no-code/build/Agda/Auto/Auto.o: No such file or directory
#   ...
#
# Thus, ignore exit code.

.PHONY: type-check
type-check:
	@echo "================= Type checking using Cabal with -fno-code ==============="
	-time $(CABAL) $(CABAL_BUILD_CMD) --builddir=$(BUILD_DIR)-no-code \
          --ghc-options=-fno-code \
          --ghc-options=-fwrite-interface \
          2>&1 \
          | $(SED) -e '/.*dist.*build.*: No such file or directory/d' \
                   -e '/.*Warning: the following files would be used as linker inputs, but linking is not being done:.*/d'


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

.PHONY : debug-install-quick ## Install Agda (compiled with -O0) with debug enabled via cabal.
debug-install-quick :
	$(QUICK_CABAL_INSTALL) --disable-library-profiling \
        -fdebug --program-suffix=-debug-quick --builddir=$(BUILD_DIR)-debug-quick \
        $(CABAL_INSTALL_BIN_OPTS) --ghc-options=-O0

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
clean_helper = if [ -d $(1) ]; then $(CABAL) $(CABAL_CLEAN_CMD) --builddir=$(1); fi;

clean : ## Clean all local builds
	$(call clean_helper,$(BUILD_DIR))
	$(call clean_helper,$(QUICK_BUILD_DIR))
	$(STACK) clean --full
	$(STACK) clean --full --work-dir=$(QUICK_STACK_BUILD_DIR)

## Haddock ###################################################################

.PHONY : haddock ##
haddock :
	$(CABAL) $(CABAL_CONFIGURE_CMD) $(CABAL_CONFIGURE_OPTS)
	$(CABAL) $(CABAL_HADDOCK_CMD) --builddir=$(BUILD_DIR)

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
	@($(MAKE) -C std-lib setup)

.PHONY : fast-forward-std-lib ##
fast-forward-std-lib :
	git submodule update --init --remote std-lib
	@($(MAKE) -C std-lib setup)

##############################################################################
## Cubical library
.PHONY : cubical ## Update the cubical library.
cubical :
	git submodule update --init cubical

.PHONY : up-to-date-cubical ##
up-to-date-cubical : cubical

.PHONY : fast-forward-cubical ##
fast-forward-cubical :
	git submodule update --init --remote cubical

##############################################################################
## Testing

.PHONY : test ## Run all test suites.
test : check-whitespace \
       common \
       succeed \
       fail \
       bugs \
       interaction \
       examples \
       std-lib-test \
       cubical-test \
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
quicktest : common succeed fail

.PHONY : bugs ##
bugs :
	@$(call decorate, "Suite of tests for bugs", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Bugs)

.PHONY : internal-tests ##
internal-tests :
	@$(call decorate, "Internal test suite", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Internal )

.PHONY : common ##
common :
	@$(call decorate, "Suite of successful tests: mini-library Common", \
		$(MAKE) -C test/Common )

.PHONY : succeed ##
succeed :
	@$(call decorate, "Suite of successful tests", \
		echo $(AGDA_BIN) > test/Succeed/exec-tc/executables && \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Succeed ; \
		rm test/Succeed/exec-tc/executables )

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
		(cd std-lib && $(RUNGHC) GenerateEverything.hs && \
						time $(AGDA_BIN) $(AGDA_OPTS) --ignore-interfaces --no-default-libraries -v profile:$(PROFVERB) \
														 -i. -isrc README.agda \
														 +RTS -s))

.PHONY : cubical-test ##
cubical-test :
	-rm -r cubical/_build
	@$(call decorate, "Cubical library test", \
		time $(MAKE) -C cubical \
                  AGDA_EXEC=$(AGDA_BIN) RTS_OPTIONS=$(AGDA_OPTS))

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

.PHONY : benchmark-summary ##
benchmark-summary :
	@$(call decorate, "Benchmark summary", \
	  $(MAKE) -C benchmark summary)

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

FIXW_PATH = src/fix-whitespace
FIXW_BIN  = $(FIXW_PATH)/dist/build/fix-whitespace/fix-whitespace

.PHONY : fix-whitespace ## Fix the whitespace issue.
fix-whitespace : $(FIXW_BIN)
	$(FIXW_BIN)

.PHONY : check-whitespace ## Check the whitespace issue without fixing it.
check-whitespace : $(FIXW_BIN)
	$(FIXW_BIN) --check

.PHONY : install-fix-whitespace ## Build fix-whitespace.
install-fix-whitespace : $(FIXW_BIN)

$(FIXW_BIN) :
	git submodule update --init src/fix-whitespace
ifdef HAS_STACK
	$(STACK) build fix-whitespace
	mkdir -p $(FIXW_PATH)/dist/build/fix-whitespace/
	cp $(shell $(STACK) path --local-install-root)/bin/fix-whitespace $(FIXW_BIN)
else
	cd $(FIXW_PATH) && $(CABAL) $(CABAL_INSTALL_CMD)
endif

## agda-bisect standalone program ############################################
.PHONY : install-agda-bisect ## Install agda-bisect.
install-agda-bisect :
	@$(call decorate, "Installing the agda-bisect program", \
		cd src/agda-bisect && $(CABAL) $(CABAL_INSTALL_CMD))

## HPC #######################################################################
.PHONY: hpc-build ##
hpc-build: ensure-hash-is-correct
	$(CABAL) $(CABAL_CLEAN_CMD) $(CABAL_OPTS)
	$(CABAL) $(CABAL_CONFIGURE_CMD) --enable-library-coverage $(CABAL_INSTALL_OPTS)
	$(CABAL) $(CABAL_BUILD_CMD) $(CABAL_OPTS)

agda.tix: ./examples/agda.tix ./test/common/agda.tix ./test/Succeed/agda.tix ./test/compiler/agda.tix ./test/api/agda.tix ./test/interaction/agda.tix ./test/fail/agda.tix ./test/lib-succeed/agda.tix ./std-lib/agda.tix ##
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
	$(MAKE) -C src/full loc

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
	@$(SED) -n \
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
	@echo "CABAL                 = $(CABAL)"
	@echo "CABAL_CONFIGURE_CMD   = $(CABAL_CONFIGURE_CMD)"
	@echo "CABAL_CONFIGURE_OPTS  = $(CABAL_CONFIGURE_OPTS)"
	@echo "CABAL_HADDOCK_CMD     = $(CABAL_HADDOCK_CMD)"
	@echo "CABAL_INSTALL_CMD     = $(CABAL_INSTALL_CMD)"
	@echo "CABAL_INSTALL_OPTS    = $(CABAL_INSTALL_OPTS)"
	@echo "CABAL_OPTS            = $(CABAL_OPTS)"
	@echo "GHC_VERSION           = $(GHC_VERSION)"
	@echo "PARALLEL_TESTS        = $(PARALLEL_TESTS)"
	@echo "STACK                 = $(STACK)"
	@echo "STACK_INSTALL_OPTS    = $(STACK_INSTALL_OPTS)"
	@echo
	@echo "Run \`make -pq\` to get a detailed report."
	@echo

# EOF
