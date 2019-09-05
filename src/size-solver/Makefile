SHELL=bash

TOP=../../
# include $(TOP)/mk/versions.mk

include $(TOP)/mk/cabal.mk

.PHONY : install-bin
install-bin :
ifneq ("$(wildcard ../../stack.yaml)","") # if `stack.yaml` exists
	stack build size-solver
	mkdir -p dist/build/size-solver
	cp $(shell stack path --local-install-root)/bin/size-solver dist/build/size-solver/size-solver
else
	$(CABAL_CMD) $(CABAL_INSTALL_CMD)
endif

# Tested with shelltestrunner 1.9.
.PHONY : test
test :
ifneq ("$(wildcard ../../stack.yaml)","") # if `stack.yaml` exists
	stack install shelltestrunner
endif
	shelltest --color --precise test/succeed.test
	shelltest --color --precise test/fail.test
