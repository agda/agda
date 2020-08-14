# ASR (04 January 2016): Not used after fixing #1753.

# Agda 2
# Makefile for successful tests depending on the standard library
# Author: Andreas Abel, Ulf Norell
# Created: 2012-02-24 (from test/succeed/Makefile)

TOP=../..

include $(TOP)/mk/paths.mk

# Verbosity
V = 1

# Getting all agda files
excluded=
allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell ls *.*agda)))
#allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell find . -name "*.agda")))
# allagda=$(patsubst %.agda,%.test,$(shell find . -name "*.agda"))
# alllagda=$(patsubst %.lagda,%.test,$(shell find . -name "*.lagda"))

default : all
all : remove_interface_files $(allagda) # $(alllagda)

# Removing all the Agda inteface files.
remove_interface_files :
	find . -type f -name '*.agdai' -delete

#  --vim

RUN_AGDA = time $(AGDA_BIN) --no-default-libraries -i. -i../../std-lib/src -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) +RTS -H1G -M1.5G -RTS

%.test : %.agda
	@echo $<
	@$(RUN_AGDA) $<
	@$(check_$*)
	@$(cleanup_$*)

%.test : %.lagda
	@echo $<
	@$(RUN_AGDA) $<
	@$(cleanup_$*)

clean :
	-rm *~

#EOF
