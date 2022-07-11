# Makefile for YAML files
# Andreas, 2021-09-13, #5556

srcpath=../../src/github/workflows
sources=$(wildcard $(srcpath)/*.yml $(srcpath)/*.yaml)
targets=$(sort $(notdir $(sources)))
json2yaml-version=0.11.8.0

# Header is not header.yml but header.txt so that is not included in $(sources).
header=$(srcpath)/header.txt

all : json2yaml-version $(targets)

# Normalize YAML files by going via JSON.
# This expands anchors which are not understood by github workflows.

% : $(srcpath)/% $(header) Makefile
	@cp $(header) $@
	yaml2json $< | json2yaml - >> $@

# Check that correct version of json2yaml is used.
#
# Print required and actual version and check (-C) whether these two lines
# are sorted as version numbers (-V).
# From: https://stackoverflow.com/questions/4023830/how-to-compare-two-strings-in-dot-separated-version-format-in-bash
json2yaml-version:
	@(printf "$(json2yaml-version)\n%s" `json2yaml --numeric-version` | sort -V -C) || (echo "ERROR: At least version $(json2yaml-version) of json2yaml is required.  Please install, e.g. via 'make req-cabal' or 'make req-stack'." && false)

## Installing the requirements `yaml2json` and `json2yaml`

requirements: req-cabal

# The flag no-exe is by default on, we need to turn it off.
# https://github.com/snoyberg/yaml/issues/194

req-cabal:
	cabal install yaml -f-no-exe

STACK_OPTS = --system-ghc
req-stack:
	stack install yaml --flag yaml:-no-exe ${STACK_OPTS}

## Debugging

debug:
	@echo "srcpath = $(srcpath)"
	@echo "targets = $(targets)"

#EOF
