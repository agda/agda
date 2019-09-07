STACK_CMD=stack

STACK_BUILD = $(STACK_CMD) build Agda --no-haddock

QUICK_STACK_BUILD_WORK_DIR = .stack-work-quick
QUICK_STACK_BUILD = $(STACK_BUILD) \
										--ghc-options=-O0 \
										--work-dir=$(QUICK_STACK_BUILD_WORK_DIR)

STACK_INSTALL_OPTS     = --flag Agda:enable-cluster-counting $(STACK_OPTS)
STACK_INSTALL_BIN_OPTS = --test \
												 --no-run-tests \
												 --no-library-profiling \
                         $(STACK_INSTALL_OPTS)



