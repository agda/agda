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
# Issue1241/TheTest must be excluded, since it is custom (see below).
excluded=./Issue1241/TheTest.lagda ./Epic.agda
allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell find . -name "*.agda")))
# allagda=$(patsubst %.agda,%.test,$(shell find . -name "*.agda"))
alllagda=$(patsubst %.lagda,%.test,$(filter-out $(excluded),$(shell find . -name "*.lagda")))

default : all
all : $(allagda) $(alllagda)

RUN_AGDA = $(AGDA_BIN) -i. -i.. --vim $(AGDA_TEST_FLAGS) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi)

check_CompilingCoinduction  = ./checkOutput ./CompilingCoinduction a
check_UniversePolymorphicIO = ./checkOutput ./UniversePolymorphicIO ok

check_Issue481 = diff Issue481.dot.orig Issue481.dot
cleanup_Issue481 = rm Issue481.dot

does_compile = $(shell if [ -e $1.flags ]; then grep compile $1.flags; fi)
cleanup	     = $(if $(call does_compile,$1),rm -rf MAlonzo $1,true)

Issue1241.test : Issue1241.lagda
	@echo $<
	@$(AGDA_BIN) $(AGDA_TEST_FLAGS) -v$(V) --latex -i Issue1241 Issue1241/TheTest.lagda

%.test : %.agda
	@echo $<
	@$(RUN_AGDA) $<
	@$(check_$*)
	@$(cleanup_$*)
	@$(call cleanup,$*)

%.test : %.lagda
	@echo $<
	@$(RUN_AGDA) $<
	@$(cleanup_$*)
	@rm -rf MAlonzo $*

clean :
	-rm *~

#EOF
