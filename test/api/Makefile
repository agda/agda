TOP = ../..

include $(TOP)/mk/paths.mk

AGDA = $(AGDA_BIN) -v0

all : Issue1168 PrettyInterface

%.agdai : %.agda $(AGDA_BIN)
	$(AGDA) $<

Issue1168 : Issue1168.agdai Issue1168.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o /tmp/$@ $@.hs
	/tmp/$@
	@rm /tmp/$@

PrettyInterface : PrettyInterface.agdai PrettyInterface.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o /tmp/$@ $@.hs
	/tmp/$@
	@rm /tmp/$@

clean :
	rm -f *.agdai *.hi *.o
