# Top-level Makefile for Agda 2
# Authors: Ulf Norell, Nils Anders Danielsson, Francesco Mazzoli, Liang-Ting Chen

# Profiling settings for std-lib-test
PROFILEOPTS=--profile=internal

# Various paths and commands

TOP=.

include ./mk/cabal.mk
include ./mk/stack.mk

# mk/path.mk uses TOP, so include after the definition of TOP.
# It also uses HAS_STACK, so include after stack.mk.
# Note that paths.mk also loads common.mk (which loads config.mk) and ghc.mk.
include ./mk/paths.mk

# mk/pretty.mk defines 'decorate'.
include ./mk/pretty.mk

# Run in interactive and parallel mode by default

# You can use the PARALLEL_TESTS variable to control the number of parallel
# tests. The default is one per processor. Invoke make like this:
#   make PARALLEL_TESTS=123 test
# Or set it in ./mk/config.mk, which is .gitignored
PARALLEL_TESTS ?= $(shell getconf _NPROCESSORS_ONLN)

AGDA_BIN_SUFFIX = -$(VERSION)
AGDA_TESTS_OPTIONS ?=-i -j$(PARALLEL_TESTS)

# A cabal/stack dictionary

CABAL_OPT_NO_DOCS = --disable-documentation
STACK_OPT_NO_DOCS = --no-haddock

CABAL_OPT_TESTS   = --enable-tests
STACK_OPT_TESTS   = --test --no-run-tests

CABAL_OPT_FAST    = --ghc-options=-O0 -fdebug
STACK_OPT_FAST    = --fast --flag Agda:debug

CABAL_FLAG_ICU    = -fenable-cluster-counting
STACK_FLAG_ICU    = --flag Agda:enable-cluster-counting

CABAL_FLAG_OPTIM_HEAVY ?= -foptimise-heavily
STACK_FLAG_OPTIM_HEAVY ?= --flag Agda:optimise-heavily

CABAL_INSTALL_HELPER = $(CABAL) $(CABAL_INSTALL_CMD) $(CABAL_OPT_NO_DOCS)
STACK_INSTALL_HELPER = $(STACK) build Agda $(STACK_OPT_NO_DOCS)

# 2016-07-15. We use a different build directory in the quick
# installation for avoiding recompilation (see Issue #2083 and
# https://github.com/haskell/cabal/issues/1893).

# quicker install: -O0, no tests

QUICK_CABAL_INSTALL = $(CABAL_INSTALL_HELPER) $(CABAL_OPT_FAST) --builddir=$(QUICK_BUILD_DIR)
QUICK_STACK_INSTALL = $(STACK_INSTALL_HELPER) $(STACK_OPT_FAST) --work-dir=$(QUICK_STACK_WORK_DIR)

# fast install: -O0, but tests

FAST_CABAL_INSTALL = $(CABAL_INSTALL_HELPER) $(CABAL_OPT_TESTS) $(CABAL_OPT_FAST) --builddir=$(FAST_BUILD_DIR)
FAST_STACK_INSTALL = $(STACK_INSTALL_HELPER) $(STACK_OPT_TESTS) $(STACK_OPT_FAST) --work-dir=$(FAST_STACK_WORK_DIR)

# ordinary install: optimizations and tests

SLOW_CABAL_INSTALL_OPTS = $(CABAL_OPT_TESTS) $(CABAL_FLAG_OPTIM_HEAVY) --builddir=$(BUILD_DIR)
SLOW_STACK_INSTALL_OPTS = $(STACK_OPT_TESTS) $(STACK_FLAG_OPTIM_HEAVY) --work-dir=$(STACK_WORK_DIR)

CABAL_INSTALL           = $(CABAL_INSTALL_HELPER) $(SLOW_CABAL_INSTALL_OPTS)
STACK_INSTALL           = $(STACK_INSTALL_HELPER) $(SLOW_STACK_INSTALL_OPTS)

# Depending on your machine and ghc version you might want to tweak the amount of memory
# given to ghc to compile Agda. To do this set GHC_RTS_OPTS in mk/config.mk (gitignored).
ifeq ($(GHC_RTS_OPTS),)
#
ifeq ("$(shell $(GHC) --info | grep 'target word size' | cut -d\" -f4)","4")
GHC_RTS_OPTS := -M2.3G
else
GHC_RTS_OPTS := -M6G
endif
#
endif
GHC_OPTS = "+RTS -A128M $(GHC_RTS_OPTS) -RTS"

# The following options are used in several invocations of cabal
# install/configure below. They are always the last options given to
# the command.
CABAL_INSTALL_OPTS =
STACK_INSTALL_OPTS =

# Only enable cluster-counting by default for non-Windows, due to agda/agda#5012
# The msys* and mingw* strings derived from: https://stackoverflow.com/a/18434831/141513
ifeq ($(filter msys% mingw%,$(shell echo "$${OSTYPE:-unknown}")),)
  CABAL_INSTALL_OPTS += $(CABAL_FLAG_ICU)
  STACK_INSTALL_OPTS += $(STACK_FLAG_ICU)
endif

CABAL_INSTALL_OPTS += --ghc-options=$(GHC_OPTS) $(CABAL_OPTS)
STACK_INSTALL_OPTS += --ghc-options $(GHC_OPTS) $(STACK_OPTS)

# Options for building Agda's dependencies.
CABAL_INSTALL_DEP_OPTS = --only-dependencies $(CABAL_INSTALL_OPTS)
STACK_INSTALL_DEP_OPTS = --only-dependencies $(STACK_INSTALL_OPTS)

# Options for building the Agda exectutable.
# -j1 so that cabal will print built progress to stdout.
CABAL_INSTALL_BIN_OPTS         = -fdebug $(CABAL_INSTALL_BIN_OPTS_NODEBUG)
CABAL_INSTALL_BIN_OPTS_NODEBUG = -j1 --disable-library-profiling $(CABAL_INSTALL_OPTS)
STACK_INSTALL_BIN_OPTS         = --flag Agda:debug $(STACK_INSTALL_BIN_OPTS_NODEBUG)
STACK_INSTALL_BIN_OPTS_NODEBUG = --no-library-profiling $(STACK_INSTALL_OPTS)

CABAL_CONFIGURE_OPTS = $(SLOW_CABAL_INSTALL_OPTS) \
                       --disable-library-profiling \
                       $(CABAL_INSTALL_OPTS)

##############################################################################
## Installation (via stack if stack.yaml is present)

.PHONY: default
default: install-bin

.PHONY: install ## Install Agda with standard flags, compile and setup Emacs mode
install:
ifdef HAS_STACK
	$(STACK) install --ghc-options $(GHC_OPTS) $(STACK_OPTS)
else
	$(CABAL) install --ghc-options=$(GHC_OPTS) $(CABAL_OPTS)
endif
	agda --setup --emacs-mode compile --emacs-mode setup

.PHONY: setup-agda
setup-agda:
	$(AGDA_BIN) --setup

# GHC doesn't realise that the Template Haskell changes in the VersionCommit module
# even if the source code does not. Simply touching the source is not enough to force
# GHC to rebuild, so we remove the object file from the build directory.
.PHONY: ensure-hash-is-correct
ensure-hash-is-correct:
	rm -f $(BUILD_DIR)/build/Agda/VersionCommit.o
	rm -f $(BUILD_DIR)/build/agda-mode/agda-mode-tmp/Agda/VersionCommit.o

.PHONY: copy-bins-with-suffix-% ## Copy binaries to local bin directory with suffix
copy-bins-with-suffix-%:
ifdef HAS_STACK
	mkdir -p $(shell $(STACK) path --local-bin)
	cp $(shell $(STACK) --work-dir=$(STACK_WORK_DIR) path --dist-dir)/build/agda/agda $(shell $(STACK) path --local-bin)/agda-$*
	cp $(shell $(STACK) --work-dir=$(STACK_WORK_DIR) path --dist-dir)/build/agda-mode/agda-mode $(shell $(STACK) path --local-bin)/agda-mode-$*
endif

.PHONY: install-deps ## Install Agda dependencies.
install-deps:
ifdef IN_NIX_SHELL
	@echo "===================== Dependencies provided by Nix, skipping install ====="
else ifdef HAS_STACK
	@echo "===================== Installing dependencies using Stack ================"
	time $(STACK_INSTALL) $(STACK_INSTALL_DEP_OPTS)
else
	@echo "========================= Installing dependencies using Cabal ============"
	time $(CABAL_INSTALL) $(CABAL_INSTALL_DEP_OPTS)
endif

.PHONY: install-bin ## Install Agda and test suites
install-bin: install-deps ensure-hash-is-correct
ifdef HAS_STACK
	@echo "===================== Installing using Stack with test suites ============"
	time $(STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
	$(MAKE) copy-bins-with-suffix$(AGDA_BIN_SUFFIX)
else
# `cabal new-install --enable-tests` emits the error message (bug?):
# cabal: --enable-tests was specified, but tests can't be enabled in a remote package
	@echo "===================== Installing using Cabal with test suites ============"
	time $(CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS) --program-suffix=$(AGDA_BIN_SUFFIX)
endif

.PHONY: install-bin-no-debug ## Install Agda and test suites with debug printing disabled
install-bin-no-debug: install-deps ensure-hash-is-correct
ifdef HAS_STACK
	@echo "===================== Installing using Stack with test suites ============"
	time $(STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS_NODEBUG)
	$(MAKE) copy-bins-with-suffix$(AGDA_BIN_SUFFIX)
else
# `cabal new-install --enable-tests` emits the error message (bug?):
# cabal: --enable-tests was specified, but tests can't be enabled in a remote package
	@echo "===================== Installing using Cabal with test suites ============"
	time $(CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS_NODEBUG) --program-suffix=$(AGDA_BIN_SUFFIX)
endif

.PHONY: v1-install ## Developer install goal without -foptimize-aggressively nor dependencies.
	# Alternative to 'install-bin'
v1-install:  ensure-hash-is-correct
ifdef HAS_STACK
	@echo "===================== Installing using Stack with test suites ============"
	time $(STACK_INSTALL_HELPER) $(STACK_INSTALL_BIN_OPTS) $(STACK_OPT_TESTS)
	$(MAKE) copy-bins-with-suffix$(AGDA_BIN_SUFFIX)
else
	@echo "===================== Installing using Cabal with test suites ============"
	time $(CABAL_INSTALL_HELPER) $(CABAL_INSTALL_BIN_OPTS) $(CABAL_OPT_TESTS) --builddir=$(BUILD_DIR) --program-suffix=$(AGDA_BIN_SUFFIX)
endif

.PHONY: fast-install-bin ## Install Agda compiled with -O0 with tests
fast-install-bin: install-deps fast-install-bin-no-deps

.PHONY: fast-install-bin-no-deps ##
 fast-install-bin-no-deps:
ifdef HAS_STACK
	@echo "============= Installing using Stack with -O0 and test suites ============"
	time $(FAST_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
	$(MAKE) copy-bins-with-suffix-fast STACK_WORK_DIR=$(FAST_STACK_WORK_DIR)
else
# `cabal new-install --enable-tests` emits the error message (bug?):
# cabal: --enable-tests was specified, but tests can't be enabled in a remote package
	@echo "============= Installing using Cabal with -O0 and test suites ============"
	time $(FAST_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS) --program-suffix=-fast
endif

.PHONY: quicker-install-bin ## Install Agda compiled with -O0 without tests
# Disabling optimizations leads to *much* quicker build times.
# The performance loss is acceptable for running small tests.
quicker-install-bin: install-deps quicker-install-bin-no-deps

.PHONY: quicker-install-bin-no-deps ##
quicker-install-bin-no-deps:
ifdef HAS_STACK
	@echo "===================== Installing using Stack with -O0 ===================="
	time $(QUICK_STACK_INSTALL) $(STACK_INSTALL_BIN_OPTS)
	$(MAKE) copy-bins-with-suffix-quicker STACK_WORK_DIR=$(QUICK_STACK_WORK_DIR)
else
	@echo "===================== Installing using Cabal with -O0 ===================="
	time $(QUICK_CABAL_INSTALL) $(CABAL_INSTALL_BIN_OPTS) --program-suffix=-quicker
endif

.PHONY: v2-type-check ## Type check the Agda source only (-fno-code) with v2-cabal.
# Takes max 40s; can be quicker than make quicker-install-bin (max 5min).
#
# Might "fail" with errors like
#
#   ar: ./dist-2.6.2-no-code/build/Agda/Auto/Auto.o: No such file or directory
#   ...
#
# Thus, ignore exit code.
# Also prefixing it with `time` has no effect since it formally fails.
v2-type-check:
	@echo "=============== Type checking using v2 Cabal with -fno-code =============="
	-$(CABAL) v2-build --project-file=cabal.project.tc --builddir=dist-no-code \
          2>&1 \
          | $(SED) -e '/.*dist.*build.*: No such file or directory/d' \
                   -e '/.*Warning: the following files would be used as linker inputs, but linking is not being done:.*/d'

# Andreas, 2022-01-30:
# According to my experiments, `make type-check-no-deps` on an
# unchanged project runs slightly faster than `make v2-type-check`.
# Thus keeping the `v1` style as the default.

.PHONY: type-check ## Type check the Agda source only (-fno-code) with v1-cabal.
# Takes max 40s; can be quicker than make quicker-install-bin (max 5min).
#
# Might "fail" with errors like
#
#   ar: ./dist-2.6.2-no-code/build/Agda/Auto/Auto.o: No such file or directory
#   ...
#
# Thus, ignore exit code.
# Also prefixing it with `time` has no effect since it formally fails.
type-check: install-deps type-check-no-deps

.PHONY: type-check-no-deps ##
type-check-no-deps :
	@echo "=============== Type checking using v1 Cabal with -fno-code =============="
	-$(CABAL) v1-build --builddir=$(BUILD_DIR)-no-code \
	  --ghc-options=-fno-code \
	  --ghc-options=-fwrite-interface \
	  --ghc-options=-fwrite-ide-info \
	  --ghc-options=-hiedir=dist-hiefiles \
          2>&1 \
          | $(SED) -e '/.*dist.*build.*: No such file or directory/d' \
                   -e '/.*Warning: the following files would be used as linker inputs, but linking is not being done:.*/d'

# The default is to not include cost centres for libraries, but to
# include cost centres for Agda using -fprof-late. (The use of
# -fprof-late might lead to more informative profiles than if
# -fprof-auto had been used.)
PROFILING_DETAIL=\
  --profiling-detail=none\
  --ghc-options=-fprof-late

.PHONY : install-prof-bin ## Install Agda with profiling enabled
# --program-suffix is not for the executable name in
# $(BUILD_DIR)/build/, only for installing it into .cabal/bin
install-prof-bin : install-deps ensure-hash-is-correct
	$(CABAL_INSTALL) -j1 \
          --enable-profiling $(PROFILING_DETAIL) \
          --program-suffix=-prof $(CABAL_INSTALL_OPTS)

##############################################################################
## Agda mode for Emacs

.PHONY : compile-emacs-mode ## Compile Agda's Emacs mode using Emacs.
compile-emacs-mode: install-bin
	$(AGDA_BIN) --emacs-mode compile

.PHONY : setup-emacs-mode ## Configure Agda's Emacs mode.
setup-emacs-mode : install-bin
	@echo
	@echo "If the agda is not found, make sure that the directory"
	@echo "in which it was installed is located on your shell's search path."
	@echo
	$(AGDA_BIN) --emacs-mode setup

##############################################################################
## Clean

clean_helper = if [ -d $(1) ]; then $(CABAL) $(CABAL_CLEAN_CMD) --builddir=$(1); fi;

clean : ## Clean all local builds
	$(call clean_helper,$(BUILD_DIR))
	$(call clean_helper,$(QUICK_BUILD_DIR))
	which $(STACK) > /dev/null 2>&1 && $(STACK) clean --full || true
	which $(STACK) > /dev/null 2>&1 && $(STACK) clean --full --work-dir=$(QUICK_STACK_WORK_DIR) || true

##############################################################################
## Haddock

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
## Create tag files

.PHONY : tags ##
tags : have-bin-hs-tags
	$(MAKE) -C $(FULL_SRC_DIR) tags

.PHONY : TAGS ##
TAGS : have-bin-hs-tags
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
## Continuous Integration

.PHONY : workflows ## Build the workflow configuration in .github/workflows.
workflows :
	make -C .github/workflows

##############################################################################
## Testing

.PHONY : test ## Run all test suites.
test : check-whitespace \
       check-encoding \
       check-mdo \
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
       doc-test \
       size-solver-test

.PHONY : test-using-std-lib ## Run all tests which use the standard library.
test-using-std-lib : std-lib-test \
                     benchmark-without-logs \
                     std-lib-compiler-test \
                     std-lib-succeed \
                     std-lib-interaction

.PHONY : test-quick ## Run successful and failing tests.
test-quick : common succeed fail

.PHONY : check-encoding ## Make sure that Parser.y is ASCII. [Issue #5465]
check-encoding :
	@$(call decorate, "Check that Parser.y is ASCII", \
          iconv -f ASCII src/full/Agda/Syntax/Parser/Parser.y > /dev/null)
# Hint: if the encoding check fails, use
#
#     pcregrep --color='auto' -n "[\x80-\xFF]" src/full/Agda/Syntax/Parser/Parser.y
#
# to find non-ASCII characters.

.PHONY : check-mdo ## Make sure we don't use LANGUAGE RecursiveDo. [Issue #7303]
check-mdo :
	@$(call decorate, "Check that RecursiveDo language extension is not used", \
          test/check-mdo.sh)

.PHONY : bugs ##
bugs :
	@$(call decorate, "Suite of tests for bugs", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Bugs)

.PHONY : internal-tests ##
internal-tests :
	@$(call decorate, "Internal test suite", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Internal )

.PHONY : fast-internal-tests ##
fast-internal-tests :
	@$(call decorate, "Internal test suite (using agda-fast)", \
		AGDA_BIN=$(AGDA_FAST_BIN) $(AGDA_FAST_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Internal )

.PHONY : common ##
common :
	@$(call decorate, "Suite of successful tests: mini-library Common", \
		$(MAKE) -C test/Common )

.PHONY : succeed ##
succeed :
	@$(call decorate, "Suite of successful tests", \
		echo $(shell which $(AGDA_BIN)) > test/helpers/exec-tc/executables && \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Succeed ; \
		rm test/helpers/exec-tc/executables )

.PHONY : fast-succeed ##
fast-succeed :
	@$(call decorate, "Suite of successful tests (using agda-fast)", \
		echo $(shell which $(AGDA_FAST_BIN)) > test/helpers/exec-tc/executables && \
		AGDA_BIN=$(AGDA_FAST_BIN) $(AGDA_FAST_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Succeed ; \
		rm test/helpers/exec-tc/executables )

.PHONY : fail ##
fail :
	@$(call decorate, "Suite of failing tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Fail)

.PHONY : fast-fail ##
fast-fail :
	@$(call decorate, "Suite of failing tests (using agda-fast)", \
		AGDA_BIN=$(AGDA_FAST_BIN) $(AGDA_FAST_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Fail)

.PHONY: build-fail-test ##
build-fail-test :
	@$(call decorate, "Suite of failing --build-library tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/BuildFail)

.PHONY: build-succeed-test ##
build-succeed-test :
	@$(call decorate, "Suite of successful --build-library tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/BuildSucceed)

.PHONY : fast-build-succeed-test ##
fast-build-succeed-test :
	@$(call decorate, "Suite of successful --build-library tests (using agda-fast)", \
		AGDA_BIN=$(AGDA_FAST_BIN) $(AGDA_FAST_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/BuildSucceed)

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
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXAndHTML/HTML)

.PHONY : latex-test ##
latex-test :
	@$(call decorate, "Suite of tests for the LaTeX backend", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXAndHTML/LaTeX)

.PHONY : latex-test ##
latex-test-quick :
	@$(call decorate, "Suite of tests for the QuickLaTeX backend", \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/LaTeXAndHTML/QuickLaTeX)

.PHONY : std-lib-test ##
std-lib-test :
	@$(call decorate, "Standard library test", \
		(cd std-lib && cabal run GenerateEverything && \
						time $(AGDA_BIN) $(AGDA_OPTS) --ignore-interfaces --no-default-libraries $(PROFILEOPTS) \
														 -i. -isrc Everything.agda \
														 +RTS -s))

.PHONY : cubical-test ##
cubical-test :
	-rm -rf cubical/_build
	@$(call decorate, "Cubical library test", \
		time $(MAKE) -C cubical \
                  AGDA_BIN=$(AGDA_BIN) RTS_OPTIONS=$(AGDA_OPTS))

.PHONY : continue-cubical-test ##
continue-cubical-test :
	@$(call decorate, "Continuing cubical library test", \
		time $(MAKE) -C cubical \
                  AGDA_BIN=$(AGDA_BIN) RTS_OPTIONS=$(AGDA_OPTS))

.PHONY : continue-std-lib-test ##
continue-std-lib-test :
	@(cd std-lib && \
          time $(AGDA_BIN) $(PROFILEOPTS) --no-default-libraries -i. -isrc Everything.agda +RTS -s)

.PHONY : cubical-succeed ##
cubical-succeed :
	@$(call decorate, "Successful tests using the cubical library", \
	  find test/CubicalSucceed -type f -name '*.agdai' -delete ; \
	  AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/CubicalSucceed)

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

.PHONY : ghc-compiler-test ##
ghc-compiler-test :
	@$(call decorate, "GHC Compiler tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Compiler/MAlonzo_Lazy --regex-exclude AllStdLib)

.PHONY : js-compiler-test ##
js-compiler-test :
	@$(call decorate, "JS Compiler tests", \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Compiler/JS_CJS_MinifiedOptimized --regex-exclude AllStdLib)

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

.PHONY : user-manual-test ## Check the Agda code embedded in the user manual.
user-manual-test :
	@$(call decorate, "User manual (test)", \
		find doc/user-manual -type f -name '*.agdai' -delete; \
		AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/UserManual)

.PHONY : user-manual-covers-options ## Test that the user manual mentions all options.
user-manual-covers-options :
	@$(call decorate, "User manual should mention all options", \
          AGDA_BIN=$(AGDA_BIN) test/doc/user-manual-covers-options.sh)

.PHONY : user-manual-covers-warnings ## Test that the user manual mentions all warnings.
user-manual-covers-warnings :
	@$(call decorate, "User manual should mention all warnings", \
          AGDA_BIN=$(AGDA_BIN) test/doc/user-manual-covers-warnings.sh)

.PHONY : test-suite-covers-warnings ## Check whether the test suite covers all warnings.
test-suite-covers-warnings :
	@$(call decorate, "Test suite should cover all warnings", \
          AGDA_BIN=$(AGDA_BIN) test/test-suite-covers-warnings.sh)

.PHONY : test-suite-covers-errors ## Check whether the test suite covers all errors.
test-suite-covers-errors :
	@$(call decorate, "Test suite should cover all errors", \
          AGDA_BIN=$(AGDA_BIN) test/test-suite-covers-errors.sh)

.PHONY : testing-emacs-mode ## Compile the emacs mode and run basic tests.
testing-emacs-mode:
	@$(call decorate, "Testing the Emacs mode", \
	  $(AGDA_BIN) --emacs-mode compile)

.PHONY : doc-test ## Install and run doctest for the Agda library.
doc-test: install-doctest run-doctest

.PHONY : install-doctest ## Install doctest for the current ghc.
install-doctest:
	@$(call decorate, "Installing doctest", \
	  $(CABAL) install doctest --ignore-project)

.PHONY : run-doctest ## Run the doctests for the Agda library.
run-doctest:
	@$(call decorate, "Running doctest", \
	  $(CABAL) repl Agda -w doctest --repl-options=-w)

## Andreas, 2025-03-04: disable the size-solver-test
#
# ##############################################################################
# ## Size solver
#
# # NB. It is necessary to install the Agda library (i.e run `
# #		make install-bin`)
# # before installing the `size-solver` program.
#
# .PHONY : install-size-solver ## Install the size solver.
# install-size-solver :
# 	@$(call decorate, "Installing the size-solver program", \
# 		$(MAKE) -C src/size-solver STACK_INSTALL_OPTS='$(SLOW_STACK_INSTALL_OPTS) $(STACK_INSTALL_BIN_OPTS)' CABAL_INSTALL_OPTS='$(SLOW_CABAL_INSTALL_OPTS) $(CABAL_INSTALL_OPTS)' install-bin)
#
# .PHONY : size-solver-test ##
# size-solver-test : install-size-solver
# 	@$(call decorate, "Testing the size-solver program", \
# 		$(MAKE) -C src/size-solver test)

##############################################################################
## Development

## Setting the `stack.yaml` file ############################################

# The variable `GHC_COMPILER` is to be defined as a command-line argument.
# For example: `make set-default-stack-file GHC_COMPILER=8.10.2`

set-default-stack-file : remove-default-stack-file ##
	ln -s stack-$(GHC_COMPILER).yaml stack.yaml

remove-default-stack-file : ##
	rm -f stack.yaml

# Installing binaries for developer services

.PHONY : have-bin-%
have-bin-% :
	@($* --help > /dev/null) || $(CABAL) install --ignore-project $*

## Whitespace-related #######################################################
# Agda can fail to compile on Windows if files which are CPP-processed
# don't end with a newline character (because we use -Werror).

FIXW_BIN   = fix-whitespace

.PHONY : fix-whitespace ## Fix the whitespace issue.
fix-whitespace : have-bin-$(FIXW_BIN)
	$(FIXW_BIN)

.PHONY : check-whitespace ## Check the whitespace issue without fixing it.
check-whitespace : have-bin-$(FIXW_BIN)
	$(FIXW_BIN) --check

## agda-bisect standalone program ############################################
.PHONY : install-agda-bisect ## Install agda-bisect.
install-agda-bisect :
	@$(call decorate, "Installing the agda-bisect program", \
		cd src/agda-bisect && $(CABAL) install)

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
	@echo "AGDA_BIN                       = $(AGDA_BIN)"
	@echo "AGDA_BIN_SUFFIX                = $(AGDA_BIN_SUFFIX)"
	@echo "AGDA_MODE                      = $(AGDA_MODE)"
	@echo "AGDA_OPTS                      = $(AGDA_OPTS)"
	@echo "AGDA_TESTS_BIN                 = $(AGDA_TESTS_BIN)"
	@echo "AGDA_TESTS_OPTIONS             = $(AGDA_TESTS_OPTIONS)"
	@echo "BUILD_DIR                      = $(BUILD_DIR)"
	@echo "CABAL                          = $(CABAL)"
	@echo "CABAL_BUILD_CMD                = $(CABAL_BUILD_CMD)"
	@echo "CABAL_CLEAN_CMD                = $(CABAL_CLEAN_CMD)"
	@echo "CABAL_CONFIGURE_CMD            = $(CABAL_CONFIGURE_CMD)"
	@echo "CABAL_CONFIGURE_OPTS           = $(CABAL_CONFIGURE_OPTS)"
	@echo "CABAL_CONFIGURE_OPTS           = $(CABAL_CONFIGURE_OPTS)"
	@echo "CABAL_FLAG_ICU                 = $(CABAL_FLAG_ICU)"
	@echo "CABAL_FLAG_OPTIM_HEAVY         = $(CABAL_FLAG_OPTIM_HEAVY)"
	@echo "CABAL_HADDOCK_CMD              = $(CABAL_HADDOCK_CMD)"
	@echo "CABAL_INSTALL                  = $(CABAL_INSTALL)"
	@echo "CABAL_INSTALL_BIN_OPTS         = $(CABAL_INSTALL_BIN_OPTS)"
	@echo "CABAL_INSTALL_BIN_OPTS_NODEBUG = $(CABAL_INSTALL_BIN_OPTS_NODEBUG)"
	@echo "CABAL_INSTALL_CMD              = $(CABAL_INSTALL_CMD)"
	@echo "CABAL_INSTALL_DEP_OPTS         = $(CABAL_INSTALL_DEP_OPTS)"
	@echo "CABAL_INSTALL_HELPER           = $(CABAL_INSTALL_HELPER)"
	@echo "CABAL_INSTALL_OPTS             = $(CABAL_INSTALL_OPTS)"
	@echo "CABAL_OPTS                     = $(CABAL_OPTS)"
	@echo "CABAL_OPT_FAST                 = $(CABAL_OPT_FAST)"
	@echo "CABAL_OPT_NO_DOCS              = $(CABAL_OPT_NO_DOCS)"
	@echo "FAST_CABAL_INSTALL             = $(FAST_CABAL_INSTALL)"
	@echo "FAST_STACK_INSTALL             = $(FAST_STACK_INSTALL)"
	@echo "GHC_OPTS                       = $(GHC_OPTS)"
	@echo "GHC_RTS_OPTS                   = $(GHC_RTS_OPTS)"
	@echo "GHC_VER                        = $(GHC_VER)"
	@echo "GHC_VERSION                    = $(GHC_VERSION)"
	@echo "PARALLEL_TESTS                 = $(PARALLEL_TESTS)"
	@echo "PROFILEOPTS                    = $(PROFILEOPTS)"
	@echo "QUICK_CABAL_INSTALL            = $(QUICK_CABAL_INSTALL)"
	@echo "QUICK_STACK_INSTALL            = $(QUICK_STACK_INSTALL)"
	@echo "SLOW_CABAL_INSTALL_OPTS        = $(SLOW_CABAL_INSTALL_OPTS)"
	@echo "SLOW_STACK_INSTALL_OPTS        = $(SLOW_STACK_INSTALL_OPTS)"
	@echo "STACK                          = $(STACK)"
	@echo "STACK_WORK_DIR                 = $(STACK_WORK_DIR)"
	@echo "STACK_FLAG_ICU                 = $(STACK_FLAG_ICU)"
	@echo "STACK_FLAG_OPTIM_HEAVY         = $(STACK_FLAG_OPTIM_HEAVY)"
	@echo "STACK_INSTALL                  = $(STACK_INSTALL)"
	@echo "STACK_INSTALL_BIN_OPTS         = $(STACK_INSTALL_BIN_OPTS)"
	@echo "STACK_INSTALL_BIN_OPTS_NODEBUG = $(STACK_INSTALL_BIN_OPTS_NODEBUG)"
	@echo "STACK_INSTALL_DEP_OPTS         = $(STACK_INSTALL_DEP_OPTS)"
	@echo "STACK_INSTALL_HELPER           = $(STACK_INSTALL_HELPER)"
	@echo "STACK_INSTALL_OPTS             = $(STACK_INSTALL_OPTS)"
	@echo "STACK_OPTS                     = $(STACK_OPTS)"
	@echo "STACK_OPT_FAST                 = $(STACK_OPT_FAST)"
	@echo "STACK_OPT_NO_DOCS              = $(STACK_OPT_NO_DOCS)"
	@echo
	@echo "Run \`make -pq\` to get a detailed report."
	@echo

# EOF
