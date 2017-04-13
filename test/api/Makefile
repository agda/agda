TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0

tmpdir := $(shell mktemp -d)

all : Issue1168.api PrettyInterface.api

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

%.api : %.agdai %.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$* $*.hs
	$(tmpdir)/$*

clean :
	rm -f *.agdai *.hi *.o
