## Tags ###################################################################

hTags=../hTags/dist/build/hTags/hTags
hTags_include=../../dist/build/autogen/cabal_macros.h ./undefined.h
hTags_flags=-i ../../dist/build/autogen/cabal_macros.h -I ./

$(hTags) : $(wildcard ../hTags/*.hs)
	$(MAKE) -C ../hTags

# create tags for VIM
tags : $(src_files) $(hTags) $(hTags_include)
	$(hTags) $(hTags_flags) -c $(src_files)

# create tags for emacs
TAGS : $(src_files) $(hTags) $(hTags_include)
	$(hTags) $(hTags_flags) -e $(src_files)

src_files=$(shell find . \( \( -name '*.hs' -o -name '*.lhs' \) ! -name '.*' \) )

src_files=$(shell find . -name '*.hs' -o -name '*.lhs')

# Andreas: create tags for everything exept Auto and Compilers
# ignore = $(patsubst ./%,%,$(shell find ./Agda/Auto ./Agda/Compiler -name '*.hs' -o -name '*.lhs'))
ignore = $(shell find ./Agda/Auto ./Agda/Compiler ./Agda/Packaging -name '*.hs' -o -name '*.lhs')
tag_files = $(filter-out $(ignore),$(src_files))

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
