
TOP = ../..
include $(TOP)/mk/paths.mk

agda = $(AGDA_BIN)

ac1 = AC.agda --ignore-interfaces
ac2 = Example.agda --ignore-interfaces
ac3 = Example.agda

foo-% :
	echo $($*)

all : test1-$(SUFFIX) test2-$(SUFFIX) test3-$(SUFFIX)

$(LOG_DIR)/%-$(SUFFIX) :
	$(agda) $($*) +RTS -s$@
	@echo "──────────────────────────────────────────────────────────────────" >> $@
	@hostinfo >> $@

