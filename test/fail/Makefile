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

# Enable read -n
SHELL=bash

# Getting all agda files
# Andreas 2010-09-24 skip over annoying Impossible.agde 
# which always changes error message because it mentions a line number in a 
# Agda source file
# 2010-09-25 reactivated
excluded=TwoCompilers.agda Issue138.agda RecordInMutual.agda
#Impossible.agda
allagda=$(filter-out $(excluded),$(shell ls *agda))
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
	@if $(agda) -i. -i.. -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) $< > $*.tmp; \
		then echo "Unexpected success"; rm -f $*.tmp; false; \
    else if [ -s $*.tmp ]; \
				 then sed -e 's/[^ (]*test.fail.//g;s/:[[:digit:]]\+:$$//' $*.tmp > $@; cat $@; rm -f $*.tmp; true; \
				 else rm -f $@ $*.tmp; false; \
				 fi; \
		fi

# Existing error

$(allstems) : % : %.err
	@echo "$*.agda"
	@if $(agda) -i. -i.. -v$(V) $(shell if [ -e $*.flags ]; then cat $*.flags; fi) $*.agda \
		 > $*.tmp.2; \
		then echo "Unexpected success"; rm -f $*.tmp.2; false; \
    else sed -e 's/[^ (]*test.fail.//g;s/\\/\//g;s/:[[:digit:]]\+:$$//' $*.tmp.2 > $*.tmp; \
				 echo `cat $*.err` | sed -e 's/\\/\//g' > $*.tmp.2; \
				 echo `cat $*.tmp` > $*.tmp.3; \
				 true; \
		fi
	@if cmp $*.tmp.2 $*.tmp.3; \
		then rm -f $*.tmp $*.tmp.2 $*.tmp.3; true; \
		else echo "== Old error ==="; \
			 cat $*.err; \
			 echo "== New error ==="; \
			 cat $*.tmp; \
			 /bin/echo -n "Accept new error [y/N]? "; \
			 read -n 1; \
			 echo ""; \
			 if [ "fckShPrg$$REPLY" != "fckShPrgy"  ]; \
			   then echo "Keeping old error"; false; \
			   else echo "Replacing error, continuing..."; \
			     mv $*.tmp $*.err; \
			     rm -f $*.tmp.2 $*.tmp.3; true; \
			 fi; \
	 fi

# Customised test cases.

.PHONY:
customised : customised/NestedProjectRoots customised/FFI

customised/NestedProjectRoots.err : %.err : %.agda
	@echo "$*.agda"
	@if ($(AGDA_BIN) --ignore-interfaces -icustomised -icustomised/Imports $*.agda; \
	    $(AGDA_BIN) -icustomised/Imports customised/Imports/A.agda; \
	    $(AGDA_BIN) -icustomised -icustomised/Imports $*.agda) > $*.tmp; \
		then echo "Unexpected success"; rm -f $*.tmp; false; \
    else if [ -s $*.tmp ]; \
		then sed -e "s/[^ (]*test.fail.//g" $*.tmp > $@; cat $@; rm -f $*.tmp; true; \
		else rm -f $@ $*.tmp; false; \
		fi; \
	fi

.PHONY:
customised/NestedProjectRoots : % : %.err
	@echo $*.agda
	-@rm -f customised/Imports/A.agdai
	-@($(AGDA_BIN) --ignore-interfaces -icustomised -icustomised/Imports $*.agda; \
	    $(AGDA_BIN) -icustomised/Imports customised/Imports/A.agda; \
	    $(AGDA_BIN) -icustomised -icustomised/Imports $*.agda) \
	    | sed -e 's/[^ (]*test.fail.//g;s/\\/\//g' \
	    > $*.err.tmp
	@echo `cat $*.err.tmp` | sed -e 's/\\/\//g' > $*.err.tmp.2
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

customised/FFI.err : %.err : %.agda
	@echo "$*.agda"
	@if ($(AGDA_BIN) --compile -v0 --ignore-interfaces -icustomised $*.agda) > $*.tmp; \
		then echo "Unexpected success"; rm -f $*.tmp; false; \
    else if [ -s $*.tmp ]; \
		then sed -e "s/[^ (]*test.fail.//g;s/[0-9][0-9]*://g;s/scope/Skopje/g" $*.tmp > $@; cat $@; rm -f $*.tmp; true; \
		else rm -f $@ $*.tmp; false; \
		fi; \
	fi

.PHONY:
customised/FFI : % : %.err
	@echo $*.agda
	-@rm -rf customised/MAlonzo
	-@$(AGDA_BIN) --compile -v0 --ignore-interfaces -icustomised $*.agda \
	    | sed -e 's/[^ (]*test.fail.//g;s/\\/\//g;s/[0-9][0-9]*://g;s/scope/Skopje/g' \
	    > $*.err.tmp
	@echo `cat $*.err.tmp` | sed -e 's/\\/\//g' > $*.err.tmp.2
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
