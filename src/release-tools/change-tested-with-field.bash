#!/bin/bash

# Update `tested-with` field in the .cabal files.

# Usage: From the repository root directory run
#   ./src/release-tools/change-tested-with-field.bash ghc_old_version ghc_new_version

ghc_old_version="$1"
ghc_new_version="$2"

files='Agda.cabal '
files+='src/agda-bisect/agda-bisect.cabal '
files+='src/release-tools/closed-issues-for-milestone/closed-issues-for-milestone.cabal '
files+='src/fix-agda-whitespace/fix-agda-whitespace.cabal '
files+='src/hTags/hTags.cabal '
files+='src/size-solver/size-solver.cabal '

for i in $files; do
    sed -i "s/GHC == $ghc_old_version/GHC == $ghc_new_version/g" $i
done
