# All makefiles must define TOP, corresponding to the Agda root directory.
# This is so that they can be imported from a Makefile in a subdirectory.
ifeq ($(TOP),)
  $(error "Makefiles must define the TOP variable to correspond with the Agda source root")
endif

# Andreas, 2025-03-05, STACK might be set in the environment
# (e.g. in workflow test.yml); in this case, don't override.
STACK ?= stack

# Andreas, 2022-03-10: suppress chatty announcements like
# "Stack has not been tested with GHC versions above 9.0, and using 9.2.2, this may fail".
# These might get in the way of interaction testing.
STACK_SILENT=$(STACK) --silent

ifneq ($(wildcard $(TOP)/stack.yaml),)
  HAS_STACK := 1
else
  HAS_STACK :=
endif
