TOP = ../..

include $(TOP)/mk/paths.mk

# Extra options when running agda --interaction
AGDA_OPT=--no-default-libraries

# Get the current directory (OS dependent).
uname:=$(shell uname)
ifeq (NT-5,$(findstring NT-5,$(uname)))
pwd=$(shell (cmd /c 'echo %CD%') | $(SED) -e 's/\\/\\\\\\\\/g')
pwdPlusDelimiter=$(pwd)\\\\
else
pwd=$(shell pwd)
pwdPlusDelimiter=$(pwd)/
endif

clean=/usr/bin/env bash $(shell pwd)/clean.sh $(SED)

# Construct the list of tests to carry out.
# Andreas, 2017-04-24 ls -t: sort by newest first
AgdaFiles=$(shell ls -t *agda)
OutFiles=$(patsubst %.lagda,%.out,$(patsubst %.agda,%.out,$(AgdaFiles)))
Tests=$(patsubst %.lagda,%.cmp,$(patsubst %.agda,%.cmp,$(AgdaFiles)))

default : $(Tests)

# TMPDIR is an absolute path because Issue6194.hs changes the working
# directory.
export TMPDIR=$(PWD)/highlighting-tmp
export BUILDDIR=_build/

# Filter out absolute pathes, make all whitespace equal, remove
# "Linking..." messages since GHC 7.0 doesn't have them.
filter=$(SED) -e 's"$(pwdPlusDelimiter)""g' \
              -e 's"$(pwd)""g' \
              -e 's" \"$(TMPDIR).*\"""' \
              -e 's"[^ (\"]*lib.prim"agda-default-include-path"g' \
              -e 's/\((agda2-info-action "\*Agda Version\*" "Agda version \([[:digit:]]\+\.\)\+[[:digit:]]\+\)\(-[[:alnum:]]\+\(-dirty\)\?\)\?\(" nil)\)/\1\5/g' \
              -e 's/\(\\n\| \)\+/ /g' \
              -e 's/^ //g' \
              -e '/Linking /d' \
              -e 's/Agda2> //g' \
     | $(clean)

# Turn off "eager failure" flags (e, E, pipefail) while running the test.
run_test=\
    set +eE +o pipefail; \
    if test -f $*.in; \
    then cat $*.in \
         | $(SED) "s/ioTCM/IOTCM/g" \
         | $(SED) "s/cmd_give/(cmd_give WithoutForce)/g" \
         | $(SED) "s/cmd_/Cmd_/g" \
         | $(SED) "s/showImplicitArgs/ShowImplicitArgs/g" \
         | $(SED) "s/toggleImplicitArgs/ToggleImplicitArgs/g" \
         | $(SED) "s/top_command/IOTCM currentFile None Indirect/g" \
         | $(SED) "s/goal_command \\([0-9]\+\\) (\\([^)]\+\\)) \\(\"[^\"]*\"\\)/IOTCM currentFile None Indirect (\\2 \\1 noRange \\3)/g" \
         | $(SED) "s/goal_command \\([0-9]\+\\) \\([^ ]\+\\) \\(\"[^\"]*\"\\)/IOTCM currentFile None Indirect (\\2 \\1 noRange \\3)/g" \
         | $(SED) "s/currentFile/\"$(wildcard $*.agda $*.lagda)\"/g" \
         | $(SED) "s+currentFullPath+\"$(pwd)/$(wildcard $*.agda $*.lagda)\"+g" \
         | $(AGDA_BIN) -v0 -i . -i .. --interaction --ignore-interfaces $(AGDA_OPT) $(RTS_$*) \
           2>&1 | $(filter) ; \
    elif test -f $*.hs; \
    then $(RUNGHC) --ghc-arg=-v0 --ghc-arg=-w ./$*.hs $(AGDA_BIN) 2>&1 | $(filter) ; \
    else /usr/bin/env bash ./$*.sh $(AGDA_BIN) "$(RUNGHC)" > $(TMPDIR)/$*.tmp_out ; \
         cat $(TMPDIR)/$*.tmp_out | $(filter) ; \
    fi

# Note that RTS_... variables are ignored when .hs/.sh files are used.

setup_Issue591     = rm -f Issue591/M.agdai
setup_Issue2217    = rm -f Issue2217/M.agdai
setup_Highlighting = rm -f Highlighting/M.agdai
setup_Auto = $(AGDA_BIN) -v0 Auto/Prelude.agda
setup_Auto-BasicLogic = $(setup_Auto)
setup_Auto-DataConstruction = $(setup_Auto)
setup_Auto-EqualityReasoning = $(setup_Auto)
setup_Auto-IndexedDatatypes = $(setup_Auto)
setup_Auto-Misc = $(setup_Auto)
setup_Auto-Modules = $(setup_Auto)
cleanup_Issue373   = rm -rf Issue373 MAlonzo
cleanup_Issue2714  = rm -rf MAlonzo
cleanup_CompilationWarnings = rm -rf MAlonzo
setup_QuickLaTeX-Caching = rm -rf latex
cleanup_QuickLaTeX-Caching = rm -rf latex
RTS_Issue637       = +RTS -K10000 -RTS
RTS_Issue639       = --safe
RTS_Issue1785      = --library-file=issue1785.libs

# No recorded output
########################################################################

# Andreas, 2017-01-27, issue #2438
# The following rule does not work on my system.
#
#   $(OutFiles) : %.out : $(wildcard %.agda %.lagda) $(wildcard %.in %.in_ghci)
#
# According to the gnu-make manual, the wildcard command matches
# immediately, but files like %.agda or %.lagda is not what we are looking for.
# It would work if pattern matching (%) is done first.
#
# However, we can use second expansion, following
# http://make.mad-scientist.net/secondary-expansion/.
# The evaluation of the automatic variable $@ is first delayed,
# such that it remains as literal string.
# After the pattern matches, and $@ is instantiated to the stem of the target
# say Issue123, we force evaluation of Issue123*.agda which gives us
# the .agda or .lagda file.

.SECONDEXPANSION:
$(OutFiles) : %.out : $$($$@.*agda) $$($$@.in $$@.hs $$@.sh)
	@-mkdir -p $(TMPDIR)
	@$(setup_$*)
	@rm -f "$(@:.out=.agdai)"
	@echo "=== Output for $* ==="
	@$(run_test) > $@
	@cat $@
	@echo "=== End of output ==="
	@rm -rf $(TMPDIR)

# Comparing output
########################################################################

# Andreas, 2020-06-09, issue #4736
# If the output has changed, the test case is "interesting",
# thus, we sort it up for the next run by touching the .agda file.

$(Tests) : %.cmp : %.out
	@-mkdir -p $(TMPDIR)
	@$(setup_$*)
	@rm -f "$(@:.cmp=.agdai)"
	@echo $*
	@$(run_test) > $*.tmp
	@if diff -q -b $*.out $*.tmp; \
		then rm -f $*.tmp; true; \
		else \
			touch -c $*.*agda; \
			echo "=== Old output ==="; \
			cat $*.out; \
			echo "=== New output ==="; \
			cat $*.tmp; \
			echo "=== Diff ==="; \
			(  git diff --no-index --no-ext-diff -w $*.out $*.tmp || true  ) ; \
			echo -n "Accept new error [y/n/Q] (default: no)? "; \
			read -n 1; \
			echo ""; \
			if [ "fckShPrg$$REPLY" != "fckShPrgy"  ]; \
			  then echo "Keeping old output"; \
			       rm -f $*.tmp; \
                               rm -rf $(TMPDIR); \
			       if [ "$(cleanup_$*)" != "" ]; then $(cleanup_$*)"" ; fi ; \
			       [ "X$$REPLY" != "XQ" ]; \
			  else echo "Replacing output, continuing..."; \
			    mv $*.tmp $*.out; \
			    true; \
			fi; \
	 fi
	@$(cleanup_$*)
	@rm -rf $(TMPDIR) $(BUILDDIR)
