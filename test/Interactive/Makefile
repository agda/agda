# Andreas, 2014-02-12
# Tests for the (unsupported :)) Agda interactive mode

TOP=../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -I -i. -i.. --ignore-interfaces

all : Naked Issue1430

# The following tests only check that  agda -I  does not crash.

Naked :
	@echo $@
	@$(AGDA) < $@.in > /dev/null

Issue1430 :
	@echo $@
	@$(AGDA) --no-default-libraries $@.agda < $@.in > /dev/null

# Debugging the Makefile

debug :
	@echo AGDA = $(AGDA)

# EOF


