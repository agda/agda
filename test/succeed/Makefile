# Agda 2
# Makefile for successful tests
# Author: Andreas Abel, Ulf Norell
# Created: 2004-12-03

TOP=../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

# Verbosity
V = 0

# Getting all agda files
excluded=./Epic.agda
allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell find . -name "*.agda")))
# allagda=$(patsubst %.agda,%.test,$(shell find . -name "*.agda"))
alllagda=$(patsubst %.lagda,%.test,$(shell find . -name "*.lagda"))

default : all
all : $(allagda) $(alllagda)

RUN_AGDA = $(AGDA_BIN) --vim $(AGDA_TEST_FLAGS) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi)

%.test : %.agda
	@echo $<
	@$(RUN_AGDA) $<

%.test : %.lagda
	@echo $<
	@$(RUN_AGDA) $<

clean :
	-rm *~

#EOF
