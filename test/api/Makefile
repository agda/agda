TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0

tmpdir := $(shell mktemp -d)

all : Issue1168 PrettyInterface

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

Issue1168 : Issue1168.agdai Issue1168.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$@ $@.hs
	$(tmpdir)/$@

PrettyInterface : PrettyInterface.agdai PrettyInterface.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$@ $@.hs
	$(tmpdir)/$@

clean :
	rm -f *.agdai *.hi *.o
