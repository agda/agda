# Makefile for the core language implementation
# Author: Ulf Norell

## Includes ###############################################################

TOP = ../../..

include $(TOP)/mk/config.mk
include $(TOP)/mk/paths.mk

## Directories ############################################################

OUT		= $(OUT_DIR)/proto/trace

## Phony targets ##########################################################

.PHONY : default clean

## Files ##################################################################

gen_hs_files = $(OUT)/Lambda/Par.hs $(OUT)/Lambda/Lex.hs $(OUT)/Lambda/Abs.hs \
				$(OUT)/Lambda/Print.hs
all_hs_files = $(shell $(FIND) . -name '*hs') $(gen_hs_files)

## Default target #########################################################

default : lam

## Creating the output directory structure ################################

dirs		= $(shell $(FIND) . -type d -not -name CVS)
out_dirs	= $(patsubst .%,$(OUT)%,$(dirs))

$(out_dirs) :
	$(MKDIR) -p $@

## Compiling agda #########################################################

GHC_FLAGS += -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns

lam : $(out_dirs) $(all_hs_files)
	$(GHC) --make -o $@ -odir $(OUT) -hidir $(OUT) -i$(OUT) $(GHC_FLAGS) Main.hs

ghci : $(out_dirs) $(all_hs_files)
	$(GHC)i -i$(OUT) $(GHC_FLAGS) Main.hs

## BNFC rules #############################################################

$(OUT)/%/Par.y $(OUT)/%/Lex.x $(OUT)/%/Abs.hs : %.cf
	bnfc -haskell -d $<
	-rm -rf $(OUT)/$*
	mv $* $(OUT)

## Rules for happy and alex ###############################################

%.hs : %.x
	$(ALEX) $(ALEX_FLAGS) $< -o $@

%.hs : %.y
	$(HAPPY) $(HAPPY_FLAGS) --info=$*.happy.out $< -o $@

## Clean ##################################################################

debug :
	@echo $(out_dirs)

