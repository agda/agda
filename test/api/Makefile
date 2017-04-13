TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0

all : Issue1168.api PrettyInterface.api

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

%.api : %.agdai %.hs
	$(eval tmpdir = $(shell mktemp -d))
	ghc -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$* $*.hs
	$(tmpdir)/$*
	rm -r $(tmpdir)

clean :
	rm -f *.agdai *.hi *.o
