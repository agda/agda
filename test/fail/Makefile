# Agda 2
# Makefile for failing tests
# Author: Andreas Abel
# Created: 2004-12-06

# How this file works
# ===================
#
# Whenever a .agda file is modified,
# a corresponding .err file is generated to save the model error message
# for this file.  When the test suite is processed the next time, e.g.,
# after some hacking on the Agda 2 implementation, the new error message
# is compared to the saved one.  If they do not match, this is considered
# an error.  Then one has to verify the new error message is actually the
# intended one (manually), and remove the .err file.

TOP = ../..

include $(TOP)/mk/paths.mk

# Path to Agda
agda=$(AGDA_BIN)

# Verbosity default = 0, can be overridden
V = 0

# Getting all agda files
allagda=$(shell find . -name '*agda' -o -name Imports -prune -a -name '*agda')
allstems=$(patsubst %.agda,%,$(allagda))
allout=$(patsubst %.agda,%.err,$(allagda))

.PHONY : $(allstems)

default : all
all : $(allstems)

debug : 
	@echo $(allagda)

# Pure agdaLight

$(allout) : %.err : %.agda
	@echo "$*.agda"
	@if $(agda) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) $< > $*.tmp; \
		then echo "Unexpected success"; rm $*.tmp; false; \
    else if [ -s $@ ]; then sed -e "s/^.*test.fail.//g" $*.tmp > $@; cat $@; rm $*.tmp; \
					else rm $@ $*.tmp; false; fi; fi
# Agda should fail with non-empty output

$(allstems) : % : %.err
	@echo "$*.agda"
	@if $(agda) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) $*.agda \
		 > $*.tmp.2; \
		then echo "Unexpected success"; rm -f $*.tmp.2; false; \
    else sed -e "s/^.*test.fail.//g" $*.tmp.2 > $*.tmp; true; fi
	@if cmp $*.err $*.tmp; \
		then rm $*.tmp; rm $*.tmp.2; \
		else echo "== Old error ==="; \
			 cat $*.err; \
			 echo "== New error ==="; \
			 cat $*.tmp; \
			 rm $*.tmp; rm $*.tmp.2; \
			 false; \
	 fi

# Clean

clean :
	-rm *.err *.tmp *~

# EOF
