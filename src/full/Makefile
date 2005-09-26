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

src_files		= $(shell $(FIND) . -name '.hs' -o -name '.lhs')
all_hs_files	= $(src_files) $(OUT)/Syntax/Parser.hs $(OUT)/Syntax/Lexer.hs

## Phony targets ##########################################################

.PHONY : default clean 

## Default target #########################################################

default : $(OUT)/agda

## Creating the output directory structure ################################

dirs		= $(shell $(FIND) . -type d -not -name CVS)
out_dirs	= $(filter-out .,$(patsubst ./%,$(OUT)/%,$(dirs)))
out_dirs_p	= $(filter-out .,$(patsubst ./%,$(OUT_P)/%,$(dirs)))

$(out_dirs) $(out_dirs_p) :
	$(MKDIR) -p $@

## Boot files pre 6.4 #####################################################

# Before ghc 6.4 you wrote hi-boot files. In 6.4 you write hs-boot files
# which ghc compiles into hi-boot files (with a very different format from
# the ones you wrote by hand). So if we are compiling with a pre-6.4 ghc
# we have to copy the hand-written hi-boot files to the out directory.

ifeq ($(HAVE_GHC_6_4),No)

src_hi_boot_files	= $(shell $(FIND) . -name '*.hi-boot')
hi_boot_files		= $(patsubst ./%,$(OUT)/%,$(src_hi_boot_files))
hi_boot_files_p		= $(patsubst ./%,$(OUT_P)/%,$(src_hi_boot_files))

$(OUT)/%.hi-boot : $(hi_boot_files) : %.hi-boot
	cp $< $@

$(OUT_P)/%.hi-boot : $(hi_boot_files_p) : %.hi-boot
	cp $< $@

endif

## Compiling agda #########################################################

$(OUT)/agda : $(out_dirs) $(all_hs_files) $(hi_boot_files)
	$(GHC) --make -o $@ -i$(OUT) -odir $(OUT) -hidir $(OUT) $(GHC_FLAGS) Main.hs

$(OUT_P)/agda : $(out_dirs_p) $(all_hs_files) $(hi_boot_files_p)
	$(GHC) --make -o $@ -i$(OUT) -odir $(OUT_P) -hidir $(OUT_P) $(GHC_FLAGS) Main.hs -prof -auto-all

## Rules for happy and alex ###############################################

$(OUT)/%.hs : %.x
	$(ALEX) $(ALEX_FLAGS) -o $@ $<

$(OUT)/%.hs : %.y
	$(HAPPY) $(HAPPY_FLAGS) -o $@ --info=$(OUT)/$*.happy.out $<

