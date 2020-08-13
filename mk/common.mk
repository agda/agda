# All makefiles must define TOP, corresponding to the Agda root directory.
ifeq ($(TOP),)
  $(error "Makefiles must define the TOP variable to correspond with the Agda source root")
endif

# Include the user config makefile, if it exists. That file is .gitignored.
# We could do `-include …` to silently try, but that would not bail on errors.
USER_CONFIG_MK := $(TOP)/mk/config.mk
ifneq ($(wildcard $(USER_CONFIG_MK)),)
include $(USER_CONFIG_MK)
endif

# Use gsed on Mac OS instead of sed
ifeq ($(shell uname), Darwin)
  SED := gsed
else
  SED := sed
endif
