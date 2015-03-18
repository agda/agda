SHELL := /bin/bash

TOP=../..

include $(TOP)/mk/paths.mk

test:
	-rm -r Epic
	-rm -r tests/bin
	mkdir tests/bin
	$(AGDA_BIN) --epic RunTests.agda
	export AGDA_PATH=$(AGDA_BIN) && ./RunTests
