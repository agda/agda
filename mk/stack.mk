STACK=stack

# Andreas, 2022-03-10: suppress chatty announcements like
# "Stack has not been tested with GHC versions above 9.0, and using 9.2.2, this may fail".
# These might get in the way of interaction testing.
STACK_SILENT=$(STACK) --silent

ifneq ($(wildcard $(TOP)/stack.yaml),)
  HAS_STACK := 1
else
  HAS_STACK :=
endif
