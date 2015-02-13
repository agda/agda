# Andreas, 2014-02-12
# Tests for the (unsupported :)) Agda interactive mode

TOP=../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

AGDA = $(AGDA_BIN) -I -i. -i.. $(AGDA_TEST_FLAGS)

all : Naked Issue1430

# The following tests only check that  agda -I  does not crash.

Naked :
	@echo $@
	@$(AGDA) < $@.in > /dev/null

Issue1430 :
	@echo $@
	@$(AGDA) $@.agda < $@.in > /dev/null

# Debugging the Makefile

debug :
	@echo AGDA = $(AGDA)

# EOF


