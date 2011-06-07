# Makefile for ECMAScript tests
# Author: Andreas Abel, Ulf Norell, Alan Jeffrey
# Created: 2011-06-07

TOP=../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

# Getting all agda files
excluded=./TestHarness.agda
allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell find . -name "*.agda")))

default : all
all : $(allagda)

COMPILE_AGDA = $(AGDA_BIN) --js -i. -i..
RHINO = rhino

jAgda/%.js : %.agda
	@$(AGDA_BIN) --js -i. -i.. $<

%.test : test-harness.js jAgda/%.js
	@$(RHINO) $^

clean :
	-rm *~

#EOF
