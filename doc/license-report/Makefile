# Andreas Abel, 2021-01-04
#
# Generate license-report for bnfc using cabal-plan.

.PHONY: default install index.md
default: index.html

install:
	cabal install -f license-report cabal-plan
	cabal install pandoc

index.md :
	cabal-plan license-report Agda:exe:agda > $@

%.html : %.md
	pandoc -s -t html -o $@ $<

# EOF
