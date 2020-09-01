# All makefiles must define TOP, corresponding to the Agda root directory.
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
else
  # The Agda makefiles prior to PR #4841 would load `mk/parallel-test.mk`,
  # which, if existed, would be expected to define the single variable
  # `PARALLEL_TESTS`. They did not load `mk/config.mk` or expect that to exist.
  #
  # It's simpler to maintain a single source of truth for user configuration.
  # So: if the new `mk/config.mk` file does not exist, but the old
  # `mk/parallel-tests.mk` does, load it and gently nudge them toward putting
  # creating a `mk/config.mk`.
  #
  # We don't create it automatically because this loading phase may not be
  # atomic and we don't want to clobber things that aren't build targets.
  #
  # The following lines should be removed at some point in the mid future.
  DEPRECATED_PARALLEL_TESTS_MK := $(TOP)/mk/parallel-tests.mk
  ifneq ($(wildcard $(DEPRECATED_PARALLEL_TESTS_MK)),)
    ifndef DID_WARN_DEPRECATED_PARALLEL_TESTS_MK
      export DID_WARN_DEPRECATED_PARALLEL_TESTS_MK := 1
      $(warning Loading deprecated $(DEPRECATED_PARALLEL_TESTS_MK))
      $(warning Please put custom makefile options in $(USER_CONFIG_MK) instead.)
      $(warning (It can contain the line "include $$(TOP)/mk/parallel-tests.mk", if you want))
    endif
    include $(DEPRECATED_PARALLEL_TESTS_MK)
  endif
endif

# Use gsed on Mac OS instead of sed
ifeq ($(shell uname), Darwin)
  SED := gsed
else
  SED := sed
endif
