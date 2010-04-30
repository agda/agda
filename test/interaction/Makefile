TOP = ../..

include $(TOP)/mk/paths.mk
include $(TOP)/mk/config.mk

pwd=$(shell pwd)/

AgdaFiles=$(shell find . -name '*.agda')
OutFiles=$(patsubst %.agda,%.out,$(AgdaFiles))
Tests=$(patsubst %.agda,%.cmp,$(AgdaFiles))

default : $(Tests)

run_test=( echo ':mod + Agda.Interaction.GhciTop Agda.Interaction.BasicOps'; \
					 echo 'ioTCM "$*.agda" Nothing ( cmd_load_silently "$*.agda" ["."] )' ; \
					 echo 'let currentFile = "$*.agda"' ) \
				 | cat - $*.in | ghci -v0 | sed -e 's"$(pwd)""g'

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

