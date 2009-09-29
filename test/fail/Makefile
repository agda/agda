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
include $(TOP)/mk/config.mk

# Path to Agda
agda=$(AGDA_BIN) $(AGDA_TEST_FLAGS)

# Verbosity default = 0, can be overridden
V = 0

# Getting all agda files
allagda=$(shell find . -name '*.agda' -o \( -name Imports -o -name customised \) -prune -a -name '*agda')
allstems=$(patsubst %.agda,%,$(allagda))
allout=$(patsubst %.agda,%.err,$(allagda))

.PHONY : $(allstems)

default : all customised
all : $(allstems)

debug : 
	@echo $(allagda)

# No error recorded

$(allout) : %.err : %.agda
	@echo "$*.agda"
	@if $(agda) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) $< > $*.tmp; \
		then echo "Unexpected success"; rm -f $*.tmp; false; \
    else if [ -s $*.tmp ]; \
				 then sed -e "s/[^ (]*test.fail.//g" $*.tmp > $@; cat $@; rm -f $*.tmp; true; \
				 else rm -f $@ $*.tmp; false; \
				 fi; \
		fi

# Existing error

$(allstems) : % : %.err
	@echo "$*.agda"
	@if $(agda) -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) $*.agda \
		 > $*.tmp.2; \
		then echo "Unexpected success"; rm -f $*.tmp.2; false; \
    else sed -e "s/[^ (]*test.fail.//g" $*.tmp.2 > $*.tmp; \
				 echo `cat $*.err` > $*.tmp.2; \
				 echo `cat $*.tmp` > $*.tmp.3; \
				 true; \
		fi
	@if cmp $*.tmp.2 $*.tmp.3; \
		then rm -f $*.tmp $*.tmp.2 $*.tmp.3; true; \
		else echo "== Old error ==="; \
			 cat $*.err; \
			 echo "== New error ==="; \
			 cat $*.tmp; \
			 rm -f $*.tmp; rm -f $*.tmp.2; rm -f $*.tmp.3; \
			 false; \
	 fi

# Customised test cases.

.PHONY:
customised : nestedProjectRoots

.PHONY:
nestedProjectRoots : customised/NestedProjectRoots.agda
	-@rm customised/Imports/A.agdai
	-@($(AGDA_BIN) --ignore-interfaces -icustomised -icustomised/Imports $<; \
	    $(AGDA_BIN) -icustomised/Imports customised/Imports/A.agda; \
	    $(AGDA_BIN) -icustomised -icustomised/Imports $<) \
	    | sed -e "s/[^ (]*test.fail.//g" \
	    > customised/NestedProjectRoots.err.tmp
	@diff -u customised/NestedProjectRoots.err \
	         customised/NestedProjectRoots.err.tmp
	-@rm customised/NestedProjectRoots.err.tmp

# Clean

clean :
	-rm -f *.err *.tmp *~

# EOF
