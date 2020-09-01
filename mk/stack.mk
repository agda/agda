STACK=stack

ifneq ($(wildcard $(TOP)/stack.yaml),)
  HAS_STACK := 1
else
  undefine HAS_STACK
endif
