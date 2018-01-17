SHELL=bash

TOP=../../
include $(TOP)/mk/versions.mk

CABAL_CMD=cabal

.PHONY : install-bin
install-bin :
	$(CABAL_CMD) install --program-suffix=-$(VERSION)

# Tested with shelltestrunner 1.9.
.PHONY : test
test :
	shelltest --color --precise test/succeed.test
	shelltest --color --precise test/fail.test
