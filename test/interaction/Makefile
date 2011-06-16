TOP = ../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

uname:=$(shell uname)
ifeq (NT-5,$(findstring NT-5,$(uname)))
pwd=$(shell (cmd /c 'echo %CD%') | sed -e 's/\\/\\\\\\\\/g')\\\\
else
pwd=$(shell pwd)/
endif

AgdaFiles=$(shell find . -name '*.agda')
OutFiles=$(patsubst %.agda,%.out,$(AgdaFiles))
Tests=$(patsubst %.agda,%.cmp,$(AgdaFiles))

default : $(Tests)

run_test=( echo ':mod + Agda.Interaction.GhciTop Agda.Interaction.BasicOps'; \
					 echo 'let currentFile = "$*.agda"'; \
					 echo "let top_command = top_command' currentFile" ) \
				 | cat - $*.in | ghc --interactive -v0 | sed -e 's"$(pwd)""g'

cleanup_Issue373 = rm -rf Issue373 MAlonzo
cleanup_Long = rm -f highlighting.tmp

%.test : %.in %.agda
	@$(run_test)

# No recorded output
$(OutFiles) : %.out : %.agda %.in
	@rm -f "$(@:.out=.agdai)"
	@echo "=== Output for $* ==="
	@$(run_test) > $@
	@cat $@
	@echo "=== End of output ==="

# Comparing output
$(Tests) : %.cmp : %.out
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

