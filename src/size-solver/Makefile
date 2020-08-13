SHELL=bash

TOP=../../

include $(TOP)/mk/cabal.mk
include $(TOP)/mk/stack.mk

.PHONY : install-bin
install-bin :
ifneq ("$(wildcard ../../stack.yaml)","") # if `stack.yaml` exists
	$(STACK) build size-solver
	mkdir -p dist/build/size-solver
	cp $(shell $(STACK) path --local-install-root)/bin/size-solver dist/build/size-solver/size-solver
else
	$(CABAL) $(CABAL_INSTALL_CMD)
endif

# Tested with shelltestrunner 1.9.
.PHONY : test
test :
ifneq ("$(wildcard ../../stack.yaml)","") # if `stack.yaml` exists
	$(STACK) install shelltestrunner
endif
	shelltest --color --precise test/succeed.test
	shelltest --color --precise test/fail.test
