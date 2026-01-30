# All makefiles must define TOP, corresponding to the Agda root directory.
# This is so that they can be imported from a Makefile in a subdirectory.
ifeq ($(TOP),)
  $(error "Makefiles must define the TOP variable to correspond with the Agda source root")
endif

# Standard "as safe as bash can be, which isn't very" flags to eagerly detect
# problems rather than barging on through and possibly executing unsafe
# commands in an unexpected state.
#  -E inherits ERR traps on subcommands and subshells.
#  -e exits on errors.
#  -o pipefail propagates errors through piped sequences.
#  -c indicates the start of the command.
SHELL := bash
.SHELLFLAGS := -Eeu -o pipefail -c

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
