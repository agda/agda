## Tags ###################################################################

hTags=../hTags/dist/build/hTags/hTags
hTags_include=../../dist/$(VERSION)/build/autogen/cabal_macros.h

$(hTags) : $(wildcard ../hTags/*.hs)
	$(MAKE) -C ../hTags

# create tags for VIM
tags : $(src_files) $(hTags) $(hTags_include)
	$(hTags) -i$(hTags_include) -c $(src_files)

# create tags for emacs
TAGS : $(src_files) $(hTags) $(hTags_include)
	$(hTags) -i$(hTags_include) -e $(src_files)

# Andreas: create tags for everything exept Auto and Compilers
ignore = $(patsubst ./%,%,$(shell $(FIND) ./Agda/Auto ./Agda/Compiler -name '*.hs' -o -name '*.lhs'))
tag_files = $(filter-out $(ignore),$(src_files))

mytags :  $(tag_files) $(hTags) $(hTags_include)
	$(hTags) -i$(hTags_include) -e $(tag_files)
