#!/usr/bin/env sh

# Andreas, 2026-07-06

# Run this script in the agda repo root after checking out a dependabot PR.
# E.g.:
# - gh pr checkout 8765  ## dependabot PR bumping github actions
# - src/release-tools/upstream.action-bumps.sh
# - # check and commit changes
# - make workflows  ## This should not alter the .github/workflows files

mkdir -p tmp
git show > tmp/gha.patch
sed -i 's!/.github/workflows/!/src/github/workflows/!g' tmp/gha.patch
patch -F 3 < tmp/gha.patch

# EOF
