TOP = ../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/version.mk

AGDA = $(AGDA_BIN) -v0

all : Issue1168 PrettyInterface

Issue1168 : Issue1168.agdai Issue1168.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o /tmp/$@ $@.hs
	/tmp/$@
	@rm /tmp/$@

Issue1168.agdai : Issue1168.agda $(AGDA_BIN)
	$(AGDA) $<

PrettyInterface : Issue1168.agdai PrettyInterface.hs
	ghc -Wall -Werror -package Agda-$(VERSION) -o /tmp/$@ $@.hs
	/tmp/$@
	@rm /tmp/$@
