# All makefiles must define TOP, corresponding to the Agda root directory.
# This is so that they can be imported from a Makefile in a subdirectory.
ifeq ($(TOP),)
  $(error "Makefiles must define the TOP variable to correspond with the Agda source root")
endif

include $(TOP)/mk/common.mk
include $(TOP)/mk/versions.mk
include $(TOP)/mk/ghc.mk

SRC_DIR        = $(TOP)/src
MAIN_SRC_DIR   = $(SRC_DIR)/main
FULL_SRC_DIR   = $(SRC_DIR)/full

# Note: To use "dist" as the build directory (the default), modify
# BUILD_DIR below. At the time of writing GHC's recompilation checker
# doesn't seem to handle Agda very well: if you compile, switch to
# another branch, and then switch back, then many (but not all)
# modules are likely to be recompiled. However, work seems to be under
# way to improve the situation:
#
# https://ghc.haskell.org/trac/ghc/ticket/8144
# https://ghc.haskell.org/trac/ghc/ticket/4012
#
# Thus it may be worthwhile to keep the present infrastructure with
# different build directories for different versions of Agda.
#
# Andreas, 2020-10-26 further refinement:
# I often switch GHC version, so indexing v1-style build directories
# by GHC version x.y.z makes sense.

# N.B. don't use TOP here, stack anyway looks upward for stack.yaml
STACK_WORK_DIR       ?= .stack-work
QUICK_STACK_WORK_DIR ?= $(STACK_WORK_DIR)-quick
FAST_STACK_WORK_DIR  ?= $(STACK_WORK_DIR)-fast

# The basic stack command needs to always set the --work-dir.
STACK_SLOW  = $(STACK) --work-dir=$(STACK_WORK_DIR)
STACK_QUICK = $(STACK) --work-dir=$(QUICK_STACK_WORK_DIR)
STACK_FAST  = $(STACK) --work-dir=$(FAST_STACK_WORK_DIR)

# BUILD_DIR can be set in the system environment.
ifdef HAS_STACK
# Where does Stack place build/ etc.?  (Will contain e.g. the GHC version.)
  BUILD_DIR       ?= $(TOP)/$(shell $(STACK_SLOW)  path --dist-dir)
  QUICK_BUILD_DIR ?= $(TOP)/$(shell $(STACK_QUICK) path --dist-dir)
  FAST_BUILD_DIR  ?= $(TOP)/$(shell $(STACK_FAST)  path --dist-dir)
else
# Where does v1-Cabal place build/ etc.? Originally in dist/, but we refine this.
  BUILD_DIR       ?= $(TOP)/dist-$(VERSION)-ghc-$(GHC_VER)
  QUICK_BUILD_DIR ?= $(BUILD_DIR)-quick
  FAST_BUILD_DIR  ?= $(BUILD_DIR)-fast
endif

# AGDA_BIN can be set in the system environment.
AGDA_BIN ?= $(BUILD_DIR)/build/agda/agda
AGDA_BIN := $(abspath $(AGDA_BIN))

# AGDA_MODE can be set in the system environment.
AGDA_MODE ?= $(BUILD_DIR)/build/agda-mode/agda-mode
AGDA_MODE := $(abspath $(AGDA_MODE))

# AGDA_TESTS_BIN can be set in the system environment.
AGDA_TESTS_BIN ?= $(BUILD_DIR)/build/agda-tests/agda-tests
AGDA_TESTS_BIN := $(abspath $(AGDA_TESTS_BIN))

# Location of the -fast binaries for v1-cabal

AGDA_FAST_BIN ?= $(FAST_BUILD_DIR)/build/agda/agda
AGDA_FAST_BIN := $(abspath $(AGDA_FAST_BIN))

AGDA_FAST_TESTS_BIN ?= $(FAST_BUILD_DIR)/build/agda-tests/agda-tests
AGDA_FAST_TESTS_BIN := $(abspath $(AGDA_FAST_TESTS_BIN))
