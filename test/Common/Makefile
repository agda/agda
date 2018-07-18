# Agda 2
# Makefile for successful tests
# Author: Andreas Abel, Ulf Norell
# Created: 2004-12-03

TOP=../..

include $(TOP)/mk/paths.mk

# Verbosity
V = 0

# Getting all agda files
allagda=$(patsubst %.agda,%.test,$(filter-out $(excluded),$(shell find . -name "*.agda" | sort)))
# allagda=$(patsubst %.agda,%.test,$(shell find . -name "*.agda"))
alllagda=$(patsubst %.lagda,%.test,$(filter-out $(excluded),$(shell find . -name "*.lagda" | sort)))

default : all
all : $(allagda) $(alllagda)

RUN_AGDA = $(AGDA_BIN) -i. -i.. --vim --ignore-interfaces --no-libraries -v$(V) -v impossible:10

cleanup = $(if $(call does_compile,$1),rm -rf MAlonzo $1,true)

%.test : %.agda
	@echo $<
	@$(RUN_AGDA) $<
	@$(check_$*)
	@$(cleanup_$*)
	@$(call cleanup,$*)

clean :
	@rm -f *~ *.agdai .*.agda.vim

#EOF
