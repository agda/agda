# Makefile for full language.
# Author:  Ulf Norell

## Includes ###############################################################

TOP = ../..

include $(TOP)/mk/config.mk
include $(TOP)/mk/paths.mk

## Directories ############################################################

OUT		= $(FULL_OUT_DIR)
OUT_P	= $(FULL_OUT_DIR)/prof

## Source files ###########################################################

src_files		= $(patsubst ./%,%,$(shell $(FIND) . -name '*.hs' -o -name '*.lhs'))
all_hs_files	= $(src_files) $(OUT)/Agda/Syntax/Parser/Parser.hs \
							   $(OUT)/Agda/Syntax/Parser/Lexer.hs
all_hs_files_p	= $(src_files) $(OUT_P)/Agda/Syntax/Parser/Parser.hs \
							   $(OUT_P)/Agda/Syntax/Parser/Lexer.hs

h_files			= undefined.h
out_h_files		= $(patsubst %,$(OUT)/%,$(h_files))
out_p_h_files	= $(patsubst %,$(OUT_P)/%,$(h_files))

## Phony targets ##########################################################

.PHONY : default clean prof

## Default target #########################################################

default : $(OUT)/agda

## Creating the output directory structure ################################

dirs		= $(shell $(FIND) . -type d -not -name CVS)
out_dirs	= $(filter-out .,$(patsubst ./%,$(OUT)/%,$(dirs)))
out_dirs_p	= $(filter-out .,$(patsubst ./%,$(OUT_P)/%,$(dirs)))

$(out_dirs) $(out_dirs_p) :
	$(MKDIR) -p $@

## Boot files #############################################################

# hs-boot files have to be in the same place as the corresponding hs file.
# Thus we have to copy the boot files for the generated files (Lexer and
# Parser) to the out directiory.

boot_files = $(OUT)/Agda/Syntax/Parser/Lexer.hs-boot
boot_files_p = $(OUT_P)/Agda/Syntax/Parser/Lexer.hs-boot

$(OUT)/% : %
	@cp $< $@

$(OUT_P)/% : %
	@cp $< $@

## Header files ###########################################################

$(out_h_files) : $(OUT)/%.h : %.h
	@cp $< $@

$(out_p_h_files) : $(OUT_P)/%.h : %.h
	@cp $< $@

## Compatibility ##########################################################

# If we don't have ghc-6.6 we need to supply some of the libraries.

ifeq ($(HAVE_GHC_6_6),No)

GHC_FLAGS += -i$(COMPAT_SRC_DIR)

endif

## Compiling agda #########################################################

prof : $(OUT_P)/agda

GHC_FLAGS += -package QuickCheck-1.0

$(OUT)/agda : $(out_dirs) $(out_h_files) $(all_hs_files) $(boot_files)
	$(GHC) --make -o $@ -i$(OUT) -I. -odir $(OUT) -hidir $(OUT) $(GHC_FLAGS) Main.hs

$(OUT_P)/agda : $(out_dirs_p) $(out_p_h_files) $(all_hs_files_p) $(boot_files_p)
	$(GHC) --make -o $@ -i$(OUT_P) -I. -odir $(OUT_P) -hidir $(OUT_P) $(GHC_FLAGS) Main.hs -prof -auto-all

## Rules for happy and alex ###############################################

$(OUT)/%.hs : %.x
	$(ALEX) $(ALEX_FLAGS) -o $@ $<

$(OUT)/%.hs : %.y
	$(HAPPY) $(HAPPY_FLAGS) -o $@ --info=$(OUT)/$*.happy.out $<

$(OUT_P)/%.hs : %.x
	$(ALEX) $(ALEX_FLAGS) -o $@ $<

$(OUT_P)/%.hs : %.y
	$(HAPPY) $(HAPPY_FLAGS) -o $@ --info=$(OUT_P)/$*.happy.out $<

## Tags ###################################################################

hTags=../hTags/dist/build/hTags/hTags
hTags_include=../../dist/build/autogen/cabal_macros.h

$(hTags) :
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
