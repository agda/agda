TOP = ../..

include $(TOP)/mk/paths.mk

# Path to Agda
agda=$(AGDA_BIN) --ignore-interfaces

all : compiled-export Issue1252 ExportAndUse # time-compilation


time-compilation :
	@(time $(agda) --compile -i. -i../../std-lib -i../../std-lib/src --ghc-flag=-i../../std-lib/ffi \
			Main.agda +RTS -H1G -M1.5G && \
		  ./Main)

compiled-export :
	$(agda) --compile --no-main -i. -i.. \
                --compile-dir=ExportTestMAlonzo ExportTestAgda.agda \
                --ghc-flag=-i.. --ghc-flag=-i../../std-lib/ffi
	runghc -iExportTestMAlonzo -i../ -i../../std-lib/ffi ExportTest.hs | grep -q "It works!"
	rm -rf ExportTestMAlonzo MAlonzo

Issue1252 :
	$(agda) --compile --no-main Issue1252.agda
	rm -rf MAlonzo

ExportAndUse :
	$(agda) --compile --no-main ExportAndUse.agda
	rm -rf MAlonzo
