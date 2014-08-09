TOP = ../..

include $(TOP)/mk/paths.mk
AGDA = $(AGDA_BIN) -v0

Issue1168 : Issue1168.agda Issue1168.hs
	$(AGDA) $@.agda
	ghc -Wall -Werror -package Agda-$(VERSION) -o /tmp/$@ $@.hs
	/tmp/$@
