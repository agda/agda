include $(TOP)/mk/common.mk
include $(TOP)/mk/versions.mk
include $(TOP)/mk/ghc.mk

MACRO_DIR = $(TOP)/macros

SRC_DIR        = $(TOP)/src
MAIN_SRC_DIR   = $(SRC_DIR)/main
FULL_SRC_DIR   = $(SRC_DIR)/full
CORE_SRC_DIR   = $(SRC_DIR)/core
TRANSL_SRC_DIR = $(SRC_DIR)/transl
COMPAT_SRC_DIR = $(SRC_DIR)/compat

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
BUILD_DIR = $(TOP)/dist-$(VERSION)

OUT_DIR        = $(TOP)/out
FULL_OUT_DIR   = $(OUT_DIR)/full
CORE_OUT_DIR   = $(OUT_DIR)/core
TRANSL_OUT_DIR = $(OUT_DIR)/transl

DOC_DIR     = $(TOP)/doc
HADDOCK_DIR = $(DOC_DIR)/haddock

AGDA_BIN ?= $(BUILD_DIR)/build/agda/agda
AGDA_BIN := $(abspath $(AGDA_BIN))

AGDA_MODE ?= $(BUILD_DIR)/build/agda-mode/agda-mode
AGDA_MODE := $(abspath $(AGDA_MODE))

AGDA_TESTS_BIN ?= $(BUILD_DIR)/build/agda-tests/agda-tests
AGDA_TESTS_BIN := $(abspath $(AGDA_TESTS_BIN))
