# Andreas, 2015-08-11, clone of ../interaction/Makefile

TOP = ../..

include $(TOP)/mk/paths.mk

uname:=$(shell uname)
ifeq (NT-5,$(findstring NT-5,$(uname)))
pwd=$(shell (cmd /c 'echo %CD%') | $(SED) -e 's/\\/\\\\\\\\/g')
pwdPlusDelimiter=$(pwd)\\\\
else
pwd=$(shell pwd)
pwdPlusDelimiter=$(pwd)/
endif

clean=/usr/bin/env bash $(shell pwd)/clean.sh $(SED)

# Andreas, 2017-04-24 ls -t: sort by newest first
AgdaFiles=$(shell ls -t *agda)
OutFiles=$(patsubst %.lagda,%.out,$(patsubst %.agda,%.out,$(AgdaFiles)))
Tests=$(patsubst %.lagda,%.cmp,$(patsubst %.agda,%.cmp,$(AgdaFiles)))

default : $(Tests)

export TMPDIR=highlighting-tmp

# Filter out absolute pathes
filter=$(SED) -e 's"$(pwdPlusDelimiter)""g' \
              -e 's"$(pwd)""g' \
              -e 's" \"$(TMPDIR).*\"""' \
              -e 's"[^ (\"]*lib.prim"agda-default-include-path"g' \
              -e 's/\(\\n\| \)\+/ /g' \
     | $(clean)

# Turn off "eager failure" flags (e, E, pipefail) while running the test.
run_test=\
    set +eE +o pipefail; \
    if test -f $*.in; \
    then cat $*.in \
         | $(SED) "s/ioTCM/IOTCM/g" \
         | $(SED) "s/cmd_/Cmd_/g" \
         | $(SED) "s/showImplicitArgs/ShowImplicitArgs/g" \
         | $(SED) "s/toggleImplicitArgs/ToggleImplicitArgs/g" \
         | $(SED) "s/top_command/IOTCM currentFile None Indirect/g" \
         | $(SED) "s/goal_command \\([0-9]\+\\) (\\([^)]\+\\)) \\(\"[^\"]*\"\\)/IOTCM currentFile None Indirect (\\2 \\1 noRange \\3)/g" \
         | $(SED) "s/goal_command \\([0-9]\+\\) \\([^ ]\+\\) \\(\"[^\"]*\"\\)/IOTCM currentFile None Indirect (\\2 \\1 noRange \\3)/g" \
         | $(SED) "s/currentFile/\"$(wildcard $*.agda $*.lagda)\"/g" \
         | $(AGDA_BIN) -v 0 -W ignore -i . -i .. --interaction --no-default-libraries $(RTS_$*) \
           2>&1 | $(filter) ; \
    else /usr/bin/env bash ./$*.sh $(AGDA_BIN) > $(TMPDIR)/$*.tmp_out ; \
         cat $(TMPDIR)/$*.tmp_out | $(filter) ; \
    fi

# Note that RTS_... variables are ignored when .sh files are used.
# For RTS_... and setup_... variable examples, see ../interaction/Makefile.

# No recorded output
$(OutFiles) : %.out : $(wildcard %.agda %.lagda) $(wildcard %.in %.in_ghci)
	@-mkdir -p $(TMPDIR)
	@$(setup_$*)
	@rm -f "$(@:.out=.agdai)"
	@echo "=== Output for $* ==="
	@$(run_test) > $@
	@cat $@
	@echo "=== End of output ==="
	@rm -rf $(TMPDIR)

# Comparing output
$(Tests) : %.cmp : %.out
	@-mkdir -p $(TMPDIR)
	@$(setup_$*)
	@rm -f "$(@:.cmp=.agdai)"
	@echo $*
	@$(run_test) > $*.tmp
	@if diff -q -b $*.out $*.tmp; \
		then rm -f $*.tmp; true; \
		else \
			echo "=== Old output ==="; \
			cat $*.out; \
			echo "=== New output ==="; \
			cat $*.tmp; \
			echo "=== Diff ==="; \
			( git diff --no-index --no-ext-diff -w $*.out $*.tmp || true ) ; \
			/bin/echo -n "Accept new error [y/N/q]? "; \
			read -n 1; \
			echo ""; \
			if [ "fckShPrg$$REPLY" != "fckShPrgy"  ]; \
			  then echo "Keeping old output"; \
			       rm -f $*.tmp; \
                               rm -rf $(TMPDIR); \
			       if [ "$(cleanup_$*)" != "" ]; then $(cleanup_$*)"" ; fi ; \
			       [ "X$$REPLY" != "Xq" ]; \
			  else echo "Replacing output, continuing..."; \
			    mv $*.tmp $*.out; \
			    true; \
			fi; \
	 fi
	@$(cleanup_$*)
	@rm -rf $(TMPDIR)

# EOF
