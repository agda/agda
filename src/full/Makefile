
TOP=../..

include $(TOP)/mk/paths.mk

# src_files=$(shell find . \( \( -name '*.hs' -o -name '*.lhs' \) ! -name '.*' \) )
# include hs-boot files
find_filter=\( \( \( -name '*.*hs' -o -name '*.hs-boot' \) ! -name '*~' \) ! -name '.*' \)
src_files=$(shell find . $(find_filter) )


## Lines of Code ##########################################################

lexparse=./Agda/Syntax/Parser/Lexer.x ./Agda/Syntax/Parser/Parser.y
generated=./Agda/Syntax/Parser/Lexer.hs ./Agda/Syntax/Parser/Parser.hs
allsources=$(src_files) $(lexparse)
locfiles=$(filter-out $(generated),$(allsources))

utils=$(shell find Agda/Utils $(find_filter) )
syntax=$(shell find Agda/Syntax $(find_filter) )
typechecking=$(shell find Agda/TypeChecking $(find_filter) )
termination=$(shell find Agda/Termination $(find_filter) )
interaction=$(shell find Agda/Interaction $(find_filter) )
agsy=$(shell find Agda/Auto $(find_filter) )
compiler=$(shell find Agda/Compiler $(find_filter) )

locs : loc_utils loc_syntax loc_lexparse loc_typechecking loc_termination loc_interaction loc_agsy loc_compiler

loc_utils :
	@echo "========================================================================"
	@echo "== Lines of Code: Utils ================================================"
	@echo "========================================================================"
	@wc $(utils)

loc_syntax :
	@echo "========================================================================"
	@echo "== Lines of Code: Syntax, Operator Parsing, Scope Checking, Printing ==="
	@echo "========================================================================"
	@wc $(syntax)

loc_lexparse :
	@echo "========================================================================"
	@echo "== Lines of Code: ALexer and Happy-Parser =============================="
	@echo "========================================================================"
	@wc $(lexparse)

loc_typechecking :
	@echo "========================================================================"
	@echo "== Lines of Code: TypeChecking, Evaluation, Coverage, Positivity ======="
	@echo "========================================================================"
	@wc $(typechecking)

loc_termination :
	@echo "========================================================================"
	@echo "== Lines of Code: Termination =========================================="
	@echo "========================================================================"
	@wc $(termination)

loc_interaction :
	@echo "========================================================================"
	@echo "== Lines of Code: Interaction =========================================="
	@echo "========================================================================"
	@wc $(interaction)

loc_agsy :
	@echo "========================================================================"
	@echo "== Lines of Code: Agsy ================================================="
	@echo "========================================================================"
	@wc $(agsy)

loc_compiler :
	@echo "========================================================================"
	@echo "== Lines of Code: Compiler ============================================="
	@echo "========================================================================"
	@wc $(compiler)

# Total lines of code
loc :
	@wc $(locfiles)

debug_loc :
	@echo "lexparse=$(lexparse)"
	@echo "generated=$(generated)"
	@echo "allsources=$(allsources)"
	@echo "locfiles=$(locfiles)"

## Tags ###################################################################

hTags=../hTags/dist/build/hTags/hTags

CABAL_MACROS=$(BUILD_DIR)/build/autogen/cabal_macros.h

# See Issue #2419.
ifeq "$(GHC_VERSION)" "7.8"
hTags_include = $(CABAL_MACROS) ./undefined.h
hTags_flags   = -i $(CABAL_MACROS) -I ./ --cabal ../../Agda.cabal
else ifeq "$(GHC_VERSION)" "7.10"
hTags_include = $(CABAL_MACROS) ./undefined.h
hTags_flags   = -i $(CABAL_MACROS) -I ./ --cabal ../../Agda.cabal
else
hTags_include = ./undefined.h
hTags_flags   = -I ./ --cabal ../../Agda.cabal
endif

$(hTags) : $(wildcard ../hTags/*.hs)
	$(MAKE) -C ../hTags

# create tags for VIM
tags : $(src_files) $(hTags) $(hTags_include)
	$(hTags) $(hTags_flags) -c $(src_files)

# create tags for emacs
TAGS : $(src_files) $(hTags) $(hTags_include)
	$(hTags) $(hTags_flags) -e $(src_files)

# Andreas: create tags for everything exept Auto and Compilers
# ignore = $(patsubst ./%,%,$(shell find ./Agda/Auto ./Agda/Compiler -name '*.hs' -o -name '*.lhs'))
ignore = $(shell find ./Agda/Auto ./Agda/Compiler ./Agda/Packaging -name '*.hs' -o -name '*.lhs')
hs_boot = $(shell find . -name '*.hs-boot')
tag_files = $(filter-out $(hs_boot),$(filter-out $(ignore),$(src_files)))

mytags :  $(tag_files) $(hTags) $(hTags_include)
	$(hTags) $(hTags_flags) -e $(tag_files)

debug :
	@echo "Source files"
	@echo $(src_files)
	@echo "------------------------------------------------------------------------"
	@echo "Ignored files"
	@echo $(ignore)
	@echo "------------------------------------------------------------------------"
	@echo "Tag files"
	@echo $(tag_files)
# EOF
