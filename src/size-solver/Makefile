SHELL=bash

# TOP=../../
# include $(TOP)/mk/version.mk

CABAL_CMD=cabal

.PHONY : install-bin
install-bin :
	$(CABAL_CMD) install

# Tested with shelltestrunner 1.3.5.
.PHONY : test
test :
	shelltest --color --precise test/fail.test
