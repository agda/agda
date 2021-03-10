# Helpers for installing bash-completion for agda-bisect
# Andreas, 2020-01-18

.PHONY: default
default: help

agda-bisect     = $(shell which agda-bisect)
bash-completion = /etc/bash_completion.d/agda-bisect

.PHONY: help
help:
	@echo "This Makefile contains commands to install bash-completion for agda-bisect".
	@echo "Note: agda-bisect needs to be in the PATH."
	@echo "Usage: 'make linux' or 'make macos'."

## Linux

linux-bash-completion = $(bash-completion)

.PHONY: linux
linux: $(linux-bash-completion)

$(linux-bash-completion) : $(agda-bisect)
	@echo "You will be prompted for the superuser password."
	@echo "Trying to write $@."
	$(agda-bisect) --bash-completion-script $(agda-bisect) | sudo tee $@
	sudo chmod +x $@
	@echo "Done.  Now restart your bash."

## Mac OS X

macos-bash-completion = /usr/local$(bash-completion)

.PHONY: macos
macos: $(macos-bash-completion)

$(macos-bash-completion) : $(agda-bisect)
	@echo "You need bash autocompletion installed: 'brew install bash-completion'"
	@echo "Trying to write $@."
	$(agda-bisect) --bash-completion-script $(agda-bisect) | tee $@
	chmod +x $@
	@echo "Done.  Now restart your bash."

## Debugging

.PHONY: debug
debug:
	@echo "Variables:"
	@echo "agda-bisect           = $(agda-bisect)"
	@echo "linux-bash-completion = $(linux-bash-completion)"
	@echo "macos-bash-completion = $(macos-bash-completion)"

# EOF
