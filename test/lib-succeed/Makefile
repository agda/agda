
# Agda 2
# Makefile for successful tests depending on the standard library
# Author: Andreas Abel, Ulf Norell
# Created: 2012-02-24 (from test/succeed/Makefile)
SHELL=bash

TOP=../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

# Verbosity
V = 1

# Getting all agda files
excluded=
allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell ls *.*agda)))
#allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell find . -name "*.agda")))
# allagda=$(patsubst %.agda,%.test,$(shell find . -name "*.agda"))
# alllagda=$(patsubst %.lagda,%.test,$(shell find . -name "*.lagda"))

default : all
all : $(allagda) # $(alllagda)

#  --vim $(AGDA_TEST_FLAGS)

RUN_AGDA = time $(AGDA_BIN) -i. -i../../std-lib -i../../std-lib/src -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) +RTS -H1G -M1.5G -RTS

%.test : %.agda
	@echo $<
	@-rm $*.agdai
	@$(RUN_AGDA) $<
	@$(check_$*)
	@$(cleanup_$*)

%.test : %.lagda
	@echo $<
	@-rm $*.agdai
	@$(RUN_AGDA) $<
	@$(cleanup_$*)

clean :
	-rm *~

#EOF
