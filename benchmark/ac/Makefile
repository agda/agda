
TOP = ../..
include $(TOP)/mk/paths.mk

ac1 = AC.agda --ignore-interfaces
ac2 = Example.agda --ignore-interfaces
ac3 = Example.agda

foo-% :
	echo $($*)

all : test1-$(SUFFIX) test2-$(SUFFIX) test3-$(SUFFIX)

$(LOG_DIR)/%-$(SUFFIX) :
	$(AGDA_BIN) $($*) +RTS -s$@
	@echo "──────────────────────────────────────────────────────────────────" >> $@
	@hostinfo >> $@

