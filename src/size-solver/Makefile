TOP=../../

include $(TOP)/mk/cabal.mk
include $(TOP)/mk/stack.mk


STACK_INSTALL_OPTS=
CABAL_INSTALL_OPTS=

.PHONY : install-bin
install-bin :
ifdef HAS_STACK
	$(STACK) build size-solver $(STACK_INSTALL_OPTS)
	mkdir -p dist/build/size-solver
	cp $(shell $(STACK) path --local-install-root)/bin/size-solver dist/build/size-solver/size-solver
else
	$(CABAL) $(CABAL_INSTALL_CMD) $(CABAL_INSTALL_OPTS)
endif

# Tested with shelltestrunner 1.9.
.PHONY : test
test :
ifdef HAS_STACK
	$(STACK) install shelltestrunner
endif
	shelltest --color --precise test/succeed.test
	shelltest --color --precise test/fail.test
