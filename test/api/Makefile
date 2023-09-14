TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0 --no-libraries

.PHONY: all
all : Issue1168.api PrettyInterface.api PrintImports.run ScopeFromInterface.api

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

.PHONY: %.api
%.api : %.agdai %.run
	touch $@

.PHONY: %.run
%.run : %.hs
	$(eval tmpdir = $(shell mktemp -d /tmp/api-test.XXXX))
	$(GHC) -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$* $*.hs
	$(tmpdir)/$*
	rm -r $(tmpdir)

.PHONY: clean
clean :
	rm -f *.agdai *.hi *.o *.api

.PHONY: debug
debug :
	@echo "GHC     = ${GHC}"
	@echo "AGDA    = ${AGDA}"
	@echo "VERSION = ${VERSION}"

# Disable implicit rules
.SUFFIXES :
