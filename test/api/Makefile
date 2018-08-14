TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0 --no-libraries

all : Issue1168.api PrettyInterface.api ScopeFromInterface.api

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

%.api : %.agdai %.hs
	$(eval tmpdir = $(shell mktemp -d /tmp/api-test.XXXX))
ifneq ("$(wildcard ../../stack.yaml)","") # if `stack.yaml` exists
	stack ghc -- -Wall -Werror -o $(tmpdir)/$* $*.hs
else
	ghc -Wall -Werror -package Agda-$(VERSION) -o $(tmpdir)/$* $*.hs
endif
	$(tmpdir)/$*
	rm -r $(tmpdir)

clean :
	rm -f *.agdai *.hi *.o
