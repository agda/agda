# Makefile for YAML files
# Andreas, 2021-09-13, #5556

srcpath=../../src/github/workflows
sources=$(wildcard $(srcpath)/*.yml $(srcpath)/*.yaml)
targets=$(sort $(notdir $(sources)))

# Header is not header.yml but header.txt so that is not included in $(sources).
header=$(srcpath)/header.txt

all : $(targets)

# Normalize YAML files by going via JSON.
# This expands anchors which are not understood by github workflows.

% : $(srcpath)/% $(header) Makefile
	@cp $(header) $@
	yaml2json $< | json2yaml - >> $@

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
