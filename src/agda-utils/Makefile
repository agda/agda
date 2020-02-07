
TOP=../..

include $(TOP)/mk/paths.mk

# src_files=$(shell find . \( \( -name '*.hs' -o -name '*.lhs' \) ! -name '.*' \) )
# include hs-boot files
find_filter=\( \( \( -name '*.*hs' -o -name '*.hs-boot' \) ! -name '*~' \) ! -name '.*' \)
ignore_files=./Setup.hs
src_files=$(filter-out $(ignore_files),$(shell find src $(find_filter) ))


## Lines of Code ##########################################################

allsources=$(src_files)
locfiles=$(allsources)

utils=$(shell find Agda/Utils $(find_filter) )
interaction=$(shell find Agda/Interaction $(find_filter) )

locs : loc_utils loc_interaction 

loc_utils :
	@echo "========================================================================"
	@echo "== Lines of Code: Utils ================================================"
	@echo "========================================================================"
	@wc $(utils)

loc_interaction :
	@echo "========================================================================"
	@echo "== Lines of Code: Interaction =========================================="
	@echo "========================================================================"
	@wc $(interaction)

# Total lines of code
loc :
	@wc $(locfiles)

debug_loc :
	@echo "allsources=$(allsources)"
	@echo "locfiles=$(locfiles)"

## Tags ###################################################################

hTags=../hTags/dist/build/hTags/hTags

CABAL_MACROS=$(BUILD_DIR)/build/autogen/cabal_macros.h

hTags_flags   = --cabal ../../Agda.cabal

$(hTags) : $(wildcard ../hTags/*.hs)
	$(MAKE) -C ../hTags

# create tags for VIM
tags : $(src_files) $(hTags)
	$(hTags) $(hTags_flags) -c $(src_files)

# create tags for emacs
TAGS : $(src_files) $(hTags)
	$(hTags) $(hTags_flags) -e $(src_files)

# Andreas: create tags for everything exept Auto and Compilers

hs_boot = $(shell find . -name '*.hs-boot')
tag_files = $(filter-out $(hs_boot),$(src_files))

mytags :  $(tag_files) $(hTags)
	$(hTags) $(hTags_flags) -e $(tag_files)

debug :
	@echo "Source files"
	@echo $(src_files)
	@echo "------------------------------------------------------------------------"
	@echo "Tag files"
	@echo $(tag_files)
# EOF
