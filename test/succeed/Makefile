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
allagda=$(patsubst %.agda,%,$(shell find . -name "*.agda"))
alllagda=$(patsubst %.lagda,%,$(shell find . -name "*.lagda"))

default : all
all : $(allagda) $(alllagda)

RUN_AGDA = $(AGDA_BIN) --vim $(AGDA_TEST_FLAGS) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi)

$(allagda) : % : %.agda
	@echo $<
	@$(RUN_AGDA) $<

$(alllagda) : % : %.lagda
	@echo $<
	@$(RUN_AGDA) $<

clean :
	-rm *~

#EOF
