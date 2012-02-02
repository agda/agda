TOP = ../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

uname:=$(shell uname)
ifeq (NT-5,$(findstring NT-5,$(uname)))
pwd=$(shell (cmd /c 'echo %CD%') | sed -e 's/\\/\\\\\\\\/g')\\\\
else
pwd=$(shell pwd)/
endif

AgdaFiles=$(shell find . -name '*.agda' -o -name '*.lagda')
OutFiles=$(patsubst %.lagda,%.out,$(patsubst %.agda,%.out,$(AgdaFiles)))
Tests=$(patsubst %.lagda,%.cmp,$(patsubst %.agda,%.cmp,$(AgdaFiles)))

default : $(Tests)

export TMPDIR=highlighting.tmp

run_test=( echo ':mod + Agda.Interaction.GhciTop Agda.Interaction.BasicOps'; \
					 echo 'let currentFile = "$(wildcard $*.agda $*.lagda)"'; \
					 echo "let top_command = top_command' currentFile" ) \
				 | cat - $*.in | ghc --interactive -v0 \
				 | sed -e 's"$(pwd)""g' -e 's"$(TMPDIR).*$$""'

cleanup_Issue373 = rm -rf Issue373 MAlonzo

# No recorded output
$(OutFiles) : %.out : $(wildcard %.agda %.lagda) %.in
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
	@rm -f "$(@:.cmp=.agdai)"
	@echo $*
	@$(run_test) > $*.tmp
	@if cmp $*.out $*.tmp; \
		then rm -f $*.tmp; true; \
		else \
			echo "=== Old output ==="; \
			cat $*.out; \
			echo "=== New output ==="; \
			cat $*.tmp; \
			echo "=== Diff ==="; \
			diff $*.out $*.tmp; \
			rm -f $*.tmp; \
			false; \
	 fi
	@$(cleanup_$*)
	@rm -rf $(TMPDIR)

