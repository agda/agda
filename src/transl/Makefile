# Makefile for agda to agda 2 translator.
# Author:  Ulf Norell

## Includes ###############################################################

TOP = ../..

include $(TOP)/mk/config.mk
include $(TOP)/mk/paths.mk

## Directories ############################################################

OUT		= $(TRANSL_OUT_DIR)
OUT_P	= $(TRANSL_OUT_DIR)/prof

## Source files ###########################################################

src_files		= $(shell $(FIND) . -name '*.hs' -o -name '*.lhs')
all_hs_files	= $(src_files)

## Phony targets ##########################################################

.PHONY : default clean prof

## Default target #########################################################

BIN = agda1to2

default : $(OUT)/$(BIN)

## Creating the output directory structure ################################

dirs		= $(shell $(FIND) . -type d -not -name CVS)
out_dirs	= $(OUT) $(filter-out .,$(patsubst ./%,$(OUT)/%,$(dirs)))
out_dirs_p	= $(OUT_P) $(filter-out .,$(patsubst ./%,$(OUT_P)/%,$(dirs)))

$(out_dirs) $(out_dirs_p) :
	$(MKDIR) -p $@

## Boot files pre 6.4 #####################################################

# Before ghc 6.4 you wrote hi-boot files. In 6.4 you write hs-boot files
# which ghc compiles into hi-boot files (with a very different format from
# the ones you wrote by hand). So if we are compiling with a pre-6.4 ghc
# we have to copy the hand-written hi-boot files to the out directory.

ifeq ($(HAVE_GHC_6_4),No)

src_hi_boot_files	= $(shell $(FIND) . -name '*.hi-boot')
boot_files			= $(patsubst ./%,$(OUT)/%,$(src_hi_boot_files))
boot_files_p		= $(patsubst ./%,$(OUT_P)/%,$(src_hi_boot_files))

$(OUT)/%.hi-boot : $(boot_files) : %.hi-boot
	cp $< $@

$(OUT_P)/%.hi-boot : $(boot_files_p) : %.hi-boot
	cp $< $@

else

# hs-boot files have to be in the same place as the corresponding hs file.
# Thus we have to copy the boot files for the generated files (Lexer and
# Parser) to the out directiory.

boot_files =

$(OUT)/% : %
	@cp $< $@

endif

## Compiling agda #########################################################

prof : $(OUT_P)/$(BIN)

GHC_FLAGS := $(filter-out -Werror,$(GHC_FLAGS))

$(OUT)/$(BIN) : $(out_dirs) $(all_hs_files) $(boot_files)
	$(GHC) --make -o $@ -iagda -i$(FULL_SRC_DIR) -I. -odir $(OUT) -hidir $(OUT) $(GHC_FLAGS) Main.hs

$(OUT_P)/$(BIN) : $(out_dirs_p) $(all_hs_files) $(boot_files_p)
	$(GHC) --make -o $@ -iagda -i$(FULL_SRC_DIR) -I. -odir $(OUT_P) -hidir $(OUT_P) $(GHC_FLAGS) Main.hs -prof -auto-all

## Rules for happy and alex ###############################################

$(OUT)/%.hs : %.x
	$(ALEX) $(ALEX_FLAGS) -o $@ $<

$(OUT)/%.hs : %.y
	$(HAPPY) $(HAPPY_FLAGS) -o $@ --info=$(OUT)/$*.happy.out $<

## Clean

clean	:
	-rm *~
	-rm $(OUT)/$(BIN)

realclean :
	make clean
	-find $(OUT) -name '*.hi' | xargs rm
	-find $(OUT) -name '*.o'  | xargs rm

## Run agda1to2

# run	: $(OUT)/$(BIN)
# 	$(OUT)/$(BIN) test.agda1


## Testing

AGDA2=$(TOP)/out/full/agda
WORK=./examples

%.test	: $(OUT)/$(BIN)
	$(OUT)/$(BIN) -D $(WORK)/$*.agda | $(GHC) -e "getContents>>=putStr.unlines.(\"module $* where\":).map (\"  \"++).lines" > $(WORK)/$*.ag2
	-$(AGDA2) $(WORK)/$*.ag2
	$(GHC) -e "getContents>>=sequence_ . zipWith (Text.Printf.printf \"%5d: %s\n\") ([1..]::[Int]) . lines" < $(WORK)/$*.ag2
