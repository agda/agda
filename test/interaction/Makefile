TOP = ../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

# Enable read -n and 2>&1 |.
SHELL=bash

uname:=$(shell uname)
ifeq (NT-5,$(findstring NT-5,$(uname)))
pwd=$(shell (cmd /c 'echo %CD%') | sed -e 's/\\/\\\\\\\\/g')\\\\
else
pwd=$(shell pwd)/
endif

AgdaFiles=$(shell ls *agda)
OutFiles=$(patsubst %.lagda,%.out,$(patsubst %.agda,%.out,$(AgdaFiles)))
Tests=$(patsubst %.lagda,%.cmp,$(patsubst %.agda,%.cmp,$(AgdaFiles)))

default : $(Tests)

export TMPDIR=highlighting-tmp

run_test=if test -f $*.in; \
    then cat $*.in \
         | sed "s/goal_command/ioTCMgoal currentFile None/g" \
         | sed "s/top_command/ioTCM currentFile None/g" \
         | sed "s/currentFile/\"$(wildcard $*.agda $*.lagda)\"/g" \
         | agda --interaction $(RTS_$*) \
           2>&1 | sed -e 's"$(pwd)""g' -e 's"$(TMPDIR).*$$""'; \
    else source ./$*.script \
	 | sed -e 's"$(pwd)""g' -e 's"$(TMPDIR).*$$""'; \
    fi

# Note that RTS_... variables are ignored when .script files are used.

setup_Issue591     = rm -f Issue591/M.agdai
setup_Highlighting = rm -f Highlighting/M.agdai
cleanup_Issue373   = rm -rf Issue373 MAlonzo
RTS_Issue637       = +RTS -K8 -RTS
RTS_Issue639       = --safe

# No recorded output
$(OutFiles) : %.out : $(wildcard %.agda %.lagda) $(wildcard %.in %.in_ghci)
	@-mkdir $(TMPDIR)
	@$(setup_$*)
	@rm -f "$(@:.out=.agdai)"
	@echo "=== Output for $* ==="
	@$(run_test) > $@
	@cat $@
	@echo "=== End of output ==="
	@rm -rf $(TMPDIR)

# Comparing output
$(Tests) : %.cmp : %.out
	@-mkdir $(TMPDIR)
	@$(setup_$*)
	@rm -f "$(@:.cmp=.agdai)"
	@echo $*
	@$(run_test) > $*.tmp
	@if diff -b $*.out $*.tmp; \
		then rm -f $*.tmp; true; \
		else \
			echo "=== Old output ==="; \
			cat $*.out; \
			echo "=== New output ==="; \
			cat $*.tmp; \
			echo "=== Diff ==="; \
			diff -b $*.out $*.tmp; \
			/bin/echo -n "Accept new error [y/N]? "; \
			read -n 1; \
			echo ""; \
			if [ "fckShPrg$$REPLY" != "fckShPrgy"  ]; \
			  then echo "Keeping old output"; \
			       rm -f $*.tmp; \
                               rm -rf $(TMPDIR); \
			       if [ "$(cleanup_$*)" != "" ]; then $(cleanup_$*)"" ; fi ; \
			       false; \
			  else echo "Replacing output, continuing..."; \
			    mv $*.tmp $*.out; \
			    true; \
			fi; \
	 fi
	@$(cleanup_$*)
	@rm -rf $(TMPDIR)
