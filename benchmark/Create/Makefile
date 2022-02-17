# Andreas, 2020-02-15
#
TOP=../../

include $(TOP)/mk/paths.mk
include $(TOP)/mk/ghc.mk

.PHONY : default imp-%

default: imp-300

# Benchmark nested imports with one data decl

imp-% : import-%
	time $(AGDA_BIN) +RTS -s -RTS --profile=all --ignore-interfaces -i $< $</Main.agda

import-% :
	$(RUNGHC) QuadraticImportOneData.hs $@ $*

imp0-% : import0-%
	time $(AGDA_BIN) +RTS -s -RTS --profile=all --ignore-interfaces -i $< $</Main.agda

import0-% :
	$(RUNGHC) QuadraticImportOneDataNoUsing.hs $@ $*

hs-imp-% : hs-import-%
	-rm $</*.hi $</*.o $</Main
	time $(GHC) +RTS -s -RTS -i$< $</Main.hs

hs-import-% :
	$(RUNGHC) QuadraticImportOneDataHaskell.hs $@ $*

# EOF
