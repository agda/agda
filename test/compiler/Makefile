TOP = ../..

include $(TOP)/mk/paths.mk

# Path to Agda
agda=$(AGDA_BIN) --ignore-interfaces

all : # time-compilation


time-compilation :
	@(time $(agda) --compile -i. -i../../std-lib -i../../std-lib/src --ghc-flag=-i../../std-lib/ffi \
			Main.agda +RTS -H1G -M1.5G && \
		  ./Main)

Issue223 :
	$(agda) --compile --no-main Issue223.agda
	rm -rf MAlonzo
