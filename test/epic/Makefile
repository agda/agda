
TOP=../..

include $(TOP)/mk/paths.mk

test:
	-rm -r Epic
	-rm -r tests/bin
	mkdir tests/bin
	$(AGDA_BIN) --epic RunTests.agda
	./RunTests
