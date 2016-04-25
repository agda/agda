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
agda=$(AGDA_BIN) --ignore-interfaces

# use gsed on Mac OS instead of sed
ifeq (Darwin,$(findstring Darwin,$(shell uname)))
sed=gsed
else
sed=sed
endif

clean=/bin/bash $(shell pwd)/clean.sh $(sed)

# Verbosity default = 0, can be overridden
V = 0

# Enable read -n
SHELL=bash


default : customised


# Customised test cases.

.PHONY:
customised : customised/NestedProjectRoots

customised/NestedProjectRoots.err : %.err : %.agda
	@echo "$*.agda"
	@if ($(AGDA_BIN) --ignore-interfaces --no-default-libraries -icustomised -icustomised/Imports $*.agda; \
	    $(AGDA_BIN) --no-default-libraries -icustomised/Imports customised/Imports/A.agda; \
	    $(AGDA_BIN) --no-default-libraries -icustomised -icustomised/Imports $*.agda) > $*.tmp; \
		then echo "Unexpected success"; rm -f $*.tmp; false; \
    else if [ -s $*.tmp ]; \
		then cat $*.tmp | $(clean) > $@; cat $@; rm -f $*.tmp; true; \
		else rm -f $@ $*.tmp; false; \
		fi; \
	fi

.PHONY:
customised/NestedProjectRoots : % : %.err
	@echo $*.agda
	-@rm -f customised/Imports/A.agdai
	-@($(AGDA_BIN) --ignore-interfaces --no-default-libraries -icustomised -icustomised/Imports $*.agda; \
	    $(AGDA_BIN) --no-default-libraries -icustomised/Imports customised/Imports/A.agda; \
	    $(AGDA_BIN) --no-default-libraries -icustomised -icustomised/Imports $*.agda) \
	    | $(clean) > $*.err.tmp
	@echo `cat $*.err.tmp` > $*.err.tmp.2
	@echo `cat $*.err` > $*.err.tmp.3
	@if cmp $*.err.tmp.2 $*.err.tmp.3; \
		then rm -f $*.err.tmp; rm -f $*.err.tmp.2; rm -f $*.err.tmp.3; \
				 true; \
		else echo "== Old error ==="; \
			 cat $*.err; \
			 echo "== New error ==="; \
			 cat $*.err.tmp; \
			 rm -f $*.err.tmp; rm -f $*.err.tmp.2; rm -f $*.err.tmp.3; \
			 false; \
		fi

# Clean

clean :
	-rm -f *.tmp *~

# EOF
