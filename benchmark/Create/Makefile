# Andreas, 2020-02-15
#
TOP=../../

include $(TOP)/mk/paths.mk

.PHONY : default imp-%

default: imp-300

# Benchmark nested imports with one data decl

imp-% : import-%
	time $(AGDA_BIN) +RTS -s -RTS -v profile:20 --ignore-interfaces -i $< $</Main.agda

import-% :
	runhaskell QuadraticImportOneData.hs $@ $*

imp0-% : import0-%
	time $(AGDA_BIN) +RTS -s -RTS -v profile:20 --ignore-interfaces -i $< $</Main.agda

import0-% :
	runhaskell QuadraticImportOneDataNoUsing.hs $@ $*

hs-imp-% : hs-import-%
	-rm $</*.hi $</*.o $</Main
	time ghc +RTS -s -RTS -i$< $</Main.hs

hs-import-% :
	runhaskell QuadraticImportOneDataHaskell.hs $@ $*

# EOF
