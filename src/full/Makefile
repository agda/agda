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

generated_files = Syntax/Parser.hs Syntax/Lexer.hs
all_hs_files	= $(shell $(FIND) . -name '.hs' -o -name '.lhs')
src_files		= $(filter-out $(generated_files),$(all_hs_files))

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
	$(GHC) --make -o $@ -odir $(OUT) -hidir $(OUT) $(GHC_FLAGS) Main.hs

$(OUT_P)/agda : $(out_dirs_p) $(all_hs_files) $(hi_boot_files_p)
	$(GHC) --make -o $@ -odir $(OUT_P) -hidir $(OUT_P) $(GHC_FLAGS) Main.hs -prof -auto-all

## Rules for happy and alex ###############################################

%.hs : %.x
	$(ALEX) $(ALEX_FLAGS) $<

%.hs : %.y
	$(HAPPY) $(HAPPY_FLAGS) --info=$(OUT)/$*.happy.out $<

## Clean ##################################################################

clean :
	rm -f $(generated_files)

veryclean : clean

