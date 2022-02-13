# Andreas Abel, 2021-01-04
# - 2021-02-12 AA: check for plan.json
#
# Generate license-report for Agda using cabal-plan.

.PHONY: default
default: index.html

# Install the cabal-plan tool.

.PHONY: install
install:
	cabal install -f license-report cabal-plan
	cabal install pandoc

# PHONY goal in order to rebuild the report on every invokation of `make`.

.PHONY: index.md
index.md : ../../dist-newstyle/cache/plan.json
	cabal-plan license-report Agda:exe:agda > $@

%.html : %.md
	pandoc -s -t html -o $@ $<

# If there is no cabal build plan, create one using `cabal configure`.
#
# Caveat: does not check that build plan is up-to-date!
# Reason: we do not want to accidentially

.PHONY: configure
configure: ../../dist-newstyle/cache/plan.json

../../dist-newstyle/cache/plan.json :
	cd ../..; cabal v2-configure $(CABAL_FLAGS)

CABAL_FLAGS = \
  --enable-tests \
  --enable-benchmarks \
  --enable-documentation \
  -fenable-cluster-counting \


# EOF
