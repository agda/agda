# Agda 2
# Makefile for successful tests
# Author: Andreas Abel, Ulf Norell
# Created: 2004-12-03

TOP=../..

# Pathes to agdaLight and Property.agda
agda=$(TOP)/out/full/agda

# Getting all agda files
allagda=$(patsubst %.agda,%,$(shell find . -name "*.agda"))
alllagda=$(patsubst %.lagda,%,$(shell find . -name "*.lagda"))

default : all
all : $(allagda) $(alllagda)

$(allagda) : % : %.agda
	@echo $<
	@$(agda) $<

$(alllagda) : % : %.lagda
	@echo $<
	@$(agda) $<

clean :
	-rm *~

#EOF
