TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0 --no-libraries

all : Issue1168.api PrettyInterface.api ScopeFromInterface.api

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

%.api : %.agdai %.hs
	$(eval tmpdir = $(shell mktemp -d /tmp/api-test.XXXX))
	$(GHC) -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$* $*.hs
	$(tmpdir)/$*
	rm -r $(tmpdir)

clean :
	rm -f *.agdai *.hi *.o

debug :
	@echo "GHC     = ${GHC}"
	@echo "AGDA    = ${AGDA}"
	@echo "VERSION = ${VERSION}"
