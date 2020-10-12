STACK=stack

ifneq ($(wildcard $(TOP)/stack.yaml),)
  HAS_STACK := 1
else
  HAS_STACK :=
endif
