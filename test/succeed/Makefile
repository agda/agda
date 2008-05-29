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

RUN_AGDA = $(AGDA_BIN) --emacs --vim $(AGDA_TEST_FLAGS)

$(allagda) : % : %.agda
	@echo $<
	@$(RUN_AGDA) -v$(V) $<

$(alllagda) : % : %.lagda
	@echo $<
	@$(RUN_AGDA) -v$(V) $<

clean :
	-rm *~

#EOF
